import sys  # CLI args + stderr + exit codes
from array import array  # compact C int array for trace


class FileReader:  # file IO helper class
    """Read a file as raw bytes and split into lines (SRP: file IO only)."""  # class purpose doc

    def read_lines(self, path):  # read one file path
        with open(path, "rb") as f:  # open raw bytes mode
            data = f.read()  # read full content
        parts = data.split(b"\n")  # split on newline byte
        if parts and parts[-1] == b"":  # trailing newline check
            parts.pop()  # drop last empty part
        return parts  # return line list


class MyersDiffer:  # O(ND) diff engine class
    """Minimal O(ND) diff for any sequence (SRP: diff only, OCP: generic)."""  # class purpose doc

    def diff(self, a, b):  # public diff entry point
        n = len(a)  # old seq length
        m = len(b)  # new seq length
        p = 0  # common prefix count
        while p < n and p < m and a[p] == b[p]:  # scan equal prefix
            p += 1  # extend prefix
        s = 0  # common suffix count
        while s < n - p and s < m - p and a[n - 1 - s] == b[m - 1 - s]:  # scan equal suffix
            s += 1  # extend suffix
        ops = []  # output op list
        for i in range(p):  # emit prefix equals
            ops.append((" ", i, i))  # equal op with indices
        mid_a_start = p  # middle old start
        mid_a_end = n - s  # middle old end
        mid_b_start = p  # middle new start
        mid_b_end = m - s  # middle new end
        if mid_a_start == mid_a_end:  # old middle empty
            for j in range(mid_b_start, mid_b_end):  # all new lines
                ops.append(("+", None, j))  # insert op
        elif mid_b_start == mid_b_end:  # new middle empty
            for i in range(mid_a_start, mid_a_end):  # all old lines
                ops.append(("-", i, None))  # delete op
        else:  # both middles non-empty
            sub_a = a[mid_a_start:mid_a_end]  # slice old middle
            sub_b = b[mid_b_start:mid_b_end]  # slice new middle
            try:  # disjoint fast path attempt
                if set(sub_a).isdisjoint(sub_b):  # no common item
                    for i in range(mid_a_start, mid_a_end):  # all old gone
                        ops.append(("-", i, None))  # delete op
                    for j in range(mid_b_start, mid_b_end):  # all new added
                        ops.append(("+", None, j))  # insert op
                    for k in range(s):  # emit suffix equals
                        ops.append((" ", n - s + k, m - s + k))  # equal op
                    return ops  # skip core entirely
            except TypeError:  # unhashable items case
                pass  # fall through to core
            mid_ops = self._core(sub_a, sub_b)  # run Myers core
            for kind, ai, bi in mid_ops:  # remap middle ops
                if kind == " ":  # equal in middle
                    ops.append((" ", ai + mid_a_start, bi + mid_b_start))  # shift indices
                elif kind == "-":  # delete in middle
                    ops.append(("-", ai + mid_a_start, None))  # shift old idx
                else:  # insert in middle
                    ops.append(("+", None, bi + mid_b_start))  # shift new idx
        for k in range(s):  # emit suffix equals
            ops.append((" ", n - s + k, m - s + k))  # equal op
        return ops  # return full op list

    def _core(self, a, b):  # Myers forward pass + backtrack
        n = len(a)  # old length
        m = len(b)  # new length
        if n == 0:  # old empty edge
            return [("+", None, j) for j in range(m)]  # all inserts
        if m == 0:  # new empty edge
            return [("-", i, None) for i in range(n)]  # all deletes
        # V is one flat list indexed by k + off (no dict overhead).  # memory fix note
        # trace[d] is a compact int array holding only the d+1 diagonals  # trace shape note
        # k = -d, -d+2, ..., d, so trace[d][(k + d) // 2] == V[k] after round d.  # index map note
        # Memory is about 2*D*D bytes instead of a dict copy per round.  # memory cost note
        max_d = n + m  # worst edit distance
        off = max_d + 1  # center offset for k
        v = [0] * (2 * max_d + 3)  # flat V array
        v[off + 1] = 0  # init k=+1 base
        trace = []  # per-round snapshots
        for d in range(max_d + 1):  # iterate edit distance
            for k in range(-d, d + 1, 2):  # diagonals of parity d
                ki = off + k  # flat index of k
                if k == -d or (k != d and v[ki - 1] < v[ki + 1]):  # pick down move
                    x = v[ki + 1]  # come from k+1
                else:  # pick right move
                    x = v[ki - 1] + 1  # come from k-1
                y = x - k  # derive y from k
                while x < n and y < m and a[x] == b[y]:  # follow snake
                    x += 1  # advance old
                    y += 1  # advance new
                v[ki] = x  # store furthest x
                if x >= n and y >= m:  # reached end
                    trace.append(array("i", v[off - d:off + d + 1:2]))  # save final round
                    return self._backtrack(trace, n, m)  # rebuild path
            trace.append(array("i", v[off - d:off + d + 1:2]))  # save round d
        raise AssertionError("unreachable")  # must finish earlier

    def _backtrack(self, trace, n, m):  # rebuild ops from trace
        rev = []  # reversed ops buffer
        x = n  # start old end
        y = m  # start new end
        for d in range(len(trace) - 1, -1, -1):  # walk rounds back
            cur = trace[d]  # current round array
            k = x - y  # current diagonal
            idx = (k + d) // 2  # index into cur
            x1 = cur[idx]  # furthest x here
            y1 = x1 - k  # furthest y here
            if d == 0:  # first round base
                for t in range(x1 - 1, -1, -1):  # leading equals
                    rev.append((" ", t, t))  # equal op
                x = 0  # reset old pos
                y = 0  # reset new pos
                break  # backtrack done
            prev = trace[d - 1]  # previous round array
            # In prev (round d-1), diagonal k-1 is at idx-1 and k+1 is at idx.  # prev layout note
            if k == -d or (k != d and prev[idx - 1] < prev[idx]):  # came via down
                pk = k + 1  # previous diagonal
                xp = prev[idx]  # prev x value
                yp = xp - pk  # prev y value
                x0 = xp  # snake old start
                y0 = x0 - k  # snake new start
                for t in range(x1 - x0 - 1, -1, -1):  # snake equals
                    rev.append((" ", x0 + t, y0 + t))  # equal op
                rev.append(("+", None, yp))  # insert step
                x = xp  # move old pos
                y = yp  # move new pos
            else:  # came via right
                pk = k - 1  # previous diagonal
                xp = prev[idx - 1]  # prev x value
                yp = xp - pk  # prev y value
                x0 = xp + 1  # snake old start
                y0 = yp  # snake new start
                for t in range(x1 - x0 - 1, -1, -1):  # snake equals
                    rev.append((" ", x0 + t, y0 + t))  # equal op
                rev.append(("-", xp, None))  # delete step
                x = xp  # move old pos
                y = yp  # move new pos
        rev.reverse()  # flip to forward order
        return rev  # return middle ops


class LineOutput:  # Part A formatter class
    """Build Part A bytes with delete-first blocks (SRP: formatting only)."""  # class purpose doc

    def build(self, ops, a_lines, b_lines):  # build diff bytes
        chunks = []  # output byte parts
        dels = []  # pending deletes
        inss = []  # pending inserts
        SP = b" "  # equal prefix
        DL = b"-"  # delete prefix
        IN = b"+"  # insert prefix
        NL = b"\n"  # line ending

        def flush():  # emit dels then inss
            for ln in dels:  # each delete
                chunks.append(DL + ln + NL)  # dash line
            for ln in inss:  # each insert
                chunks.append(IN + ln + NL)  # plus line
            dels.clear()  # reset deletes
            inss.clear()  # reset inserts

        for kind, ai, bi in ops:  # walk op list
            if kind == " ":  # equal op
                flush()  # flush hunk first
                chunks.append(SP + a_lines[ai] + NL)  # space line
            elif kind == "-":  # delete op
                dels.append(a_lines[ai])  # buffer old line
            else:  # insert op
                inss.append(b_lines[bi])  # buffer new line
        flush()  # flush tail hunk
        if chunks:  # non-empty output
            return b"".join(chunks)  # join bytes
        return b""  # empty diff bytes


class RangeOutput:  # char-range helper class
    """Char ranges for one paired line (SRP: range formatting only)."""  # class purpose doc

    def __init__(self, differ):  # store differ dep
        self._differ = differ  # reuse Myers engine

    def for_pair(self, old_bytes, new_bytes):  # ranges for line pair
        old_s = old_bytes.decode("utf-8")  # decode old line
        new_s = new_bytes.decode("utf-8")  # decode new line
        ops = self._differ.diff(old_s, new_s)  # char-level diff
        del_idx = []  # deleted char indices
        ins_idx = []  # inserted char indices
        for kind, ai, bi in ops:  # walk char ops
            if kind == "-":  # char delete
                del_idx.append(ai)  # record old idx
            elif kind == "+":  # char insert
                ins_idx.append(bi)  # record new idx
        return (self._fmt(del_idx), self._fmt(ins_idx))  # format both sides

    @staticmethod  # no self needed
    def _fmt(idx):  # format index list
        if not idx:  # empty list case
            return "."  # dot placeholder
        parts = []  # range parts
        s = idx[0]  # run start
        p = idx[0]  # run prev
        for v in idx[1:]:  # scan rest
            if v == p + 1:  # still contiguous
                p = v  # extend run
                continue  # next index
            parts.append(f"{s}-{p + 1}")  # close run
            s = v  # start new run
            p = v  # reset prev
        parts.append(f"{s}-{p + 1}")  # close last run
        return ",".join(parts)  # join ranges


class DiffApp:  # CLI workflow class
    """Orchestrate read -> diff -> output (SRP: workflow, DIP: injected parts)."""  # class purpose doc

    def __init__(self, reader, differ):  # inject dependencies
        self._reader = reader  # file reader
        self._differ = differ  # diff engine
        self._lines_out = LineOutput()  # line formatter
        self._range_out = RangeOutput(differ)  # range formatter

    def run_lines(self, a_path, b_path, out_buf):  # Part A command
        try:  # file errors mapped to 2
            a = self._reader.read_lines(a_path)  # read old file
            b = self._reader.read_lines(b_path)  # read new file
        except OSError as e:  # read failure
            print(f"error: cannot read file: {e}", file=sys.stderr)  # report to stderr
            return 2  # usage/IO exit code
        ops = self._differ.diff(a, b)  # compute ops
        data = self._lines_out.build(ops, a, b)  # format bytes
        if data:  # non-empty diff
            out_buf.write(data)  # write stdout
        return 0  # success code

    def run_highlight(self, a_path, b_path, out_buf):  # Part B command
        try:  # file errors mapped to 2
            a = self._reader.read_lines(a_path)  # read old file
            b = self._reader.read_lines(b_path)  # read new file
        except OSError as e:  # read failure
            print(f"error: cannot read file: {e}", file=sys.stderr)  # report to stderr
            return 2  # usage/IO exit code
        ops = self._differ.diff(a, b)  # compute ops
        chunks = []  # output byte parts
        dels = []  # pending old lines
        inss = []  # pending new lines
        SP = b" "  # equal prefix
        DL = b"-"  # delete prefix
        IN = b"+"  # insert prefix
        Q = b"?"  # range prefix
        NL = b"\n"  # line ending

        def flush_block():  # emit one hunk
            n_del = len(dels)  # delete count
            n_ins = len(inss)  # insert count
            for ln in dels:  # each delete
                chunks.append(DL + ln + NL)  # dash line
            pairs = n_del if n_del < n_ins else n_ins  # paired lines
            for i, ln in enumerate(inss):  # each insert
                chunks.append(IN + ln + NL)  # plus line
                if i < pairs:  # has pair
                    ro, rn = self._range_out.for_pair(dels[i], ln)  # char ranges
                    chunks.append(Q + b" " + ro.encode() + b" | " + rn.encode() + NL)  # query line
            dels.clear()  # reset deletes
            inss.clear()  # reset inserts

        for kind, ai, bi in ops:  # walk op list
            if kind == " ":  # equal op
                flush_block()  # flush hunk first
                chunks.append(SP + a[ai] + NL)  # space line
            elif kind == "-":  # delete op
                dels.append(a[ai])  # buffer old line
            else:  # insert op
                inss.append(b[bi])  # buffer new line
        flush_block()  # flush tail hunk
        if chunks:  # non-empty output
            out_buf.write(b"".join(chunks))  # write stdout
        return 0  # success code


def main() -> int:  # CLI entry function
    if len(sys.argv) != 4 or sys.argv[1] not in ("lines", "highlight"):  # validate args
        print("usage: main.py lines|highlight A_PATH B_PATH", file=sys.stderr)  # show usage
        return 2  # usage error code
    command, a_path, b_path = sys.argv[1:]  # unpack command+paths
    app = DiffApp(FileReader(), MyersDiffer())  # wire dependencies
    if command == "lines":  # Part A mode
        return app.run_lines(a_path, b_path, sys.stdout.buffer)  # run lines
    return app.run_highlight(a_path, b_path, sys.stdout.buffer)  # run highlight


raise SystemExit(main())  # execute CLI on import
