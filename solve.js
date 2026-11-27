// Fast drop-in for makefun-diff 1.0.0: byte-identical patch, much faster search.
//
// Same rule as the reference (header of vendor/makefun-diff/index.js in the
// kit): lines split on \n only; common prefix then common suffix kept; between
// them Myers's greedy search, deletion preferred on tie, never past either
// end, no edge pruning, every run of equal lines followed; patch format
// `makefun-diff/1 old=N new=M hunks=H deleted=D inserted=I`, hunks with
// `@ os ol ns nl`, `=`/`-`/`+` lines, deletions before insertions per run,
// up to 3 kept lines of context, runs <=6 kept lines apart share a hunk,
// a bare last line written with a newline plus a `%` line, identical texts
// are the first line alone.
//
// Speed comes from: lines interned to small ints (one Map lookup per line,
// int compares in the hot loop instead of string compares), the Myers
// search over Int32Arrays with no per-path object allocation, and the
// V-trace kept as flat int slices for backtracking. No other change to
// the algorithm: the same (d, k) order, the same candidate choice, the
// same snake, so the first path to reach both ends is the same path.

const KEEP = 0;
const DELETE = 1;
const INSERT = 2;
const CONTEXT = 3;

// Interning: a line's identity is its content plus whether it ends in \n.
// Newline-terminated lines are keyed by their content (without the \n);
// the single bare last line of a text, if any, by its content in a
// separate map, so "x" (bare) and "x\n" never share an id. The maps live
// across run() calls: cases in one process share most of their lines.
const nlIds = new Map();
const bareIds = new Map();
let nextId = 0;

function internNL(part) {
  let id = nlIds.get(part);
  if (id === undefined) {
    id = nextId++;
    nlIds.set(part, id);
  }
  return id;
}

function internBare(part) {
  let id = bareIds.get(part);
  if (id === undefined) {
    id = nextId++;
    bareIds.set(part, id);
  }
  return id;
}

// Split a text into its lines' ids plus the raw parts (for patch output).
// parts[i] is line i's content without its \n; line i has a trailing \n
// iff i < parts.length - 1.
function tokenize(text) {
  const parts = text.split('\n');
  const last = parts.length - 1;
  const hasBare = parts[last] !== '';
  const n = hasBare ? parts.length : last;
  const ids = new Int32Array(n);
  for (let i = 0; i < last; i++) ids[i] = internNL(parts[i]);
  if (hasBare) ids[last] = internBare(parts[last]);
  return { ids, parts, n };
}

/**
 * The edit ops of the middle (after prefix/suffix trim) as a flat array
 * of KEEP/DELETE/INSERT, one per line, in order. Exact Myers forward
 * search with the reference's tie-break, then backtrack over the V-trace.
 */
function myersOps(a, b, N, M) {
  if (N === 0 && M === 0) return [];
  const maxD = N + M;
  // trace[d] is the V row at depth d: trace[d][k + d] holds X + 1 for the
  // furthest point on diagonal k (X = old lines consumed, 0 = no path),
  // so no separate V buffers, no fill, and no copy of the row per depth:
  // each row is written once, in place, as the depth is computed.
  const trace = new Array(maxD + 1);

  // d = 0: the snake from (0, 0).
  let x = 0;
  let y = 0;
  while (x < N && y < M && a[x] === b[y]) {
    x++;
    y++;
  }
  const row0 = new Int32Array(1);
  row0[0] = x + 1;
  trace[0] = row0;
  let D = 0;
  let finalK = 0;
  if (x === N && y === M) {
    D = 0;
  } else {
    let found = false;
    for (let d = 1; d <= maxD && !found; d++) {
      const prev = trace[d - 1];
      const row = new Int32Array(2 * d + 1);
      for (let j = 0; j <= 2 * d; j += 2) {
        const k = j - d;
        const sDown = j >= 2 ? prev[j - 2] : 0;
        const sRight = j <= 2 * d - 2 ? prev[j] : 0;
        const xDown = sDown - 1;
        const xRight = sRight - 1;
        const canDel = sDown !== 0 && xDown < N;
        const canIns = sRight !== 0 && xRight - k <= M;
        if (!canDel && !canIns) continue;
        let X;
        if (canDel && (!canIns || xDown + 1 >= xRight)) X = xDown + 1;
        else X = xRight;
        let Y = X - k;
        while (X < N && Y < M && a[X] === b[Y]) {
          X++;
          Y++;
        }
        row[j] = X + 1;
        if (X === N && Y === M) {
          D = d;
          finalK = k;
          found = true;
          break;
        }
      }
      trace[d] = row;
    }
  }

  // Backtrack from (D, finalK): walk d down, each step one edit plus
  // the snake that followed it. Collected in reverse, then flipped.
  const rev = [];
  let k = finalK;
  for (let d = D; d >= 1; d--) {
    const rowD = trace[d];
    const rowPrev = trace[d - 1];
    const curX = rowD[k + d] - 1;
    const jDown = k - 1 + (d - 1);
    const jRight = k + 1 + (d - 1);
    const sDown = jDown >= 0 && jDown < rowPrev.length ? rowPrev[jDown] : 0;
    const sRight = jRight >= 0 && jRight < rowPrev.length ? rowPrev[jRight] : 0;
    const xDown = sDown - 1;
    const xRight = sRight - 1;
    const canDel = sDown !== 0 && xDown < N;
    const canIns = sRight !== 0 && xRight - k <= M;
    const byDel = canDel ? xDown + 1 : -1;
    const byIns = canIns ? xRight : -1;
    const isDel = byDel >= byIns;
    const xAfter = isDel ? byDel : byIns;
    for (let i = xAfter; i < curX; i++) rev.push(KEEP);
    rev.push(isDel ? DELETE : INSERT);
    k = isDel ? k - 1 : k + 1;
  }
  const firstX = trace[0][0] - 1;
  for (let i = 0; i < firstX; i++) rev.push(KEEP);
  rev.reverse();
  return rev;
}

/** make.fun's own patch of input.old into input.new, as one string. */
export function run(input) {
  if (input === null || typeof input !== 'object' || typeof input.old !== 'string' || typeof input.new !== 'string') {
    throw new TypeError('makefun-diff: the input is { old, new }, two strings');
  }
  const oldT = tokenize(input.old);
  const newT = tokenize(input.new);
  const a = oldT.ids;
  const b = newT.ids;
  const n = oldT.n;
  const m = newT.n;
  const oldParts = oldT.parts;
  const newParts = newT.parts;

  // Common prefix, then common suffix of what is left.
  let prefix = 0;
  while (prefix < n && prefix < m && a[prefix] === b[prefix]) prefix++;
  let suffix = 0;
  while (suffix < n - prefix && suffix < m - prefix && a[n - 1 - suffix] === b[m - 1 - suffix]) suffix++;

  const midA = a.subarray(prefix, n - suffix);
  const midB = b.subarray(prefix, m - suffix);
  const midOps = myersOps(midA, midB, midA.length, midB.length);

  // Runs: [KEEP prefix] + middle ops merged + [KEEP suffix].
  const runs = [];
  const pushRun = (kind, count) => {
    if (count <= 0) return;
    const lastR = runs[runs.length - 1];
    if (lastR !== undefined && lastR.kind === kind) lastR.count += count;
    else runs.push({ kind, count });
  };
  pushRun(KEEP, prefix);
  for (let i = 0; i < midOps.length; i++) pushRun(midOps[i], 1);
  pushRun(KEEP, suffix);

  // The change runs: each a stretch of deletions and insertions between
  // two kept lines, at old line o and new line p.
  const changes = [];
  let o = 0;
  let p = 0;
  let deleted = 0;
  let inserted = 0;
  for (const r of runs) {
    if (r.kind === KEEP) {
      o += r.count;
      p += r.count;
      continue;
    }
    let c = changes[changes.length - 1];
    if (c === undefined || c.o + c.dels !== o || c.p + c.ins !== p) {
      c = { o, p, dels: 0, ins: 0 };
      changes.push(c);
    }
    if (r.kind === DELETE) {
      c.dels += r.count;
      o += r.count;
      deleted += r.count;
    } else {
      c.ins += r.count;
      p += r.count;
      inserted += r.count;
    }
  }

  // The hunks: change runs at most 2 * CONTEXT kept lines apart share one.
  const hunks = [];
  for (const c of changes) {
    const h = hunks[hunks.length - 1];
    const prev = h !== undefined ? h[h.length - 1] : undefined;
    if (prev !== undefined && c.o - (prev.o + prev.dels) <= 2 * CONTEXT) h.push(c);
    else hunks.push([c]);
  }

  const out = [`makefun-diff/1 old=${n} new=${m} hunks=${hunks.length} deleted=${deleted} inserted=${inserted}\n`];
  const oldLast = oldParts.length - 1;
  const newLast = newParts.length - 1;
  for (const h of hunks) {
    const first = h[0];
    const last = h[h.length - 1];
    const oldStart = Math.max(0, first.o - CONTEXT);
    const newStart = first.p - (first.o - oldStart);
    const after = Math.min(CONTEXT, n - (last.o + last.dels));
    const oldEnd = last.o + last.dels + after;
    const newEnd = last.p + last.ins + after;
    out.push(`@ ${oldStart + 1} ${oldEnd - oldStart} ${newStart + 1} ${newEnd - newStart}\n`);
    let at = oldStart;
    for (const c of h) {
      for (; at < c.o; at++) out.push('=' + oldParts[at] + '\n' + (at < oldLast ? '' : '%\n'));
      for (let i = 0; i < c.dels; i++) {
        const li = c.o + i;
        out.push('-' + oldParts[li] + '\n' + (li < oldLast ? '' : '%\n'));
      }
      for (let i = 0; i < c.ins; i++) {
        const li = c.p + i;
        out.push('+' + newParts[li] + '\n' + (li < newLast ? '' : '%\n'));
      }
      at = c.o + c.dels;
    }
    for (; at < oldEnd; at++) out.push('=' + oldParts[at] + '\n' + (at < oldLast ? '' : '%\n'));
  }
  return out.join('');
}
