import sys


def split_lines(data):
    parts = data.split(b"\n")
    if parts and parts[-1] == b"":
        parts.pop()
    return parts


def read_lines(path):
    with open(path, "rb") as f:
        data = f.read()
    return split_lines(data)


def map_ids(a_lines, b_lines):
    table = {}
    nxt = 0
    A = [0] * len(a_lines)
    for i, ln in enumerate(a_lines):
        v = table.get(ln)
        if v is None:
            v = nxt
            table[ln] = v
            nxt += 1
        A[i] = v
    B = [0] * len(b_lines)
    for i, ln in enumerate(b_lines):
        v = table.get(ln)
        if v is None:
            v = nxt
            table[ln] = v
            nxt += 1
        B[i] = v
    return A, B


def myers_core(A, B):
    n = len(A)
    m = len(B)
    if n == 0:
        return [2] * m
    if m == 0:
        return [1] * n
    # fast disjoint shortcut: if no common value, trivial
    # build set of smaller side
    if n < m:
        s = set(A)
        disjoint = True
        for x in B:
            if x in s:
                disjoint = False
                break
        if disjoint:
            return [1] * n + [2] * m
    else:
        s = set(B)
        disjoint = True
        for x in A:
            if x in s:
                disjoint = False
                break
        if disjoint:
            return [1] * n + [2] * m
    V = {}
    trace = []
    D_found = -1
    NEG = -10 ** 18
    # forward
    for d in range(n + m + 1):
        cur = {}
        # local bindings
        Vget = V.get
        Ag = A
        Bg = B
        for k in range(-d, d + 1, 2):
            if k == -d or (k != d and Vget(k - 1, NEG) < Vget(k + 1, NEG)):
                x = Vget(k + 1, 0)
            else:
                x = Vget(k - 1, 0) + 1
            y = x - k
            # snake
            while x < n and y < m and Ag[x] == Bg[y]:
                x += 1
                y += 1
            cur[k] = x
            if x >= n and y >= m:
                trace.append(cur)
                D_found = d
                break
        else:
            trace.append(cur)
            V = cur
            continue
        break
    # backtrack
    ops_rev = []
    x = n
    y = m
    for d in range(D_found, 0, -1):
        Vprev = trace[d - 1]
        k = x - y
        if k == -d or (k != d and Vprev.get(k - 1, NEG) < Vprev.get(k + 1, NEG)):
            prev_k = k + 1
        else:
            prev_k = k - 1
        prev_x = Vprev.get(prev_k, 0)
        # prev_y = prev_x - prev_k (not needed explicitly)
        if prev_k == k + 1:
            # insertion
            while x > prev_x:
                ops_rev.append(0)
                x -= 1
                y -= 1
            ops_rev.append(2)
            y -= 1
        else:
            # deletion
            while x > prev_x + 1:
                ops_rev.append(0)
                x -= 1
                y -= 1
            ops_rev.append(1)
            x -= 1
    while x > 0:
        ops_rev.append(0)
        x -= 1
        y -= 1
    ops_rev.reverse()
    return ops_rev


def diff_tags(A, B):
    n = len(A)
    m = len(B)
    if n == 0:
        return [2] * m
    if m == 0:
        return [1] * n
    if A == B:
        return [0] * n
    pre = 0
    # manual loop with locals
    while pre < n and pre < m and A[pre] == B[pre]:
        pre += 1
    suf = 0
    while suf < n - pre and suf < m - pre and A[n - 1 - suf] == B[m - 1 - suf]:
        suf += 1
    if pre + suf >= n or pre + suf >= m:
        # one middle side empty (overlap cap) -> handle directly
        # e.g. A = [x], B=[x,x]: pre=1,suf=0? no overlap. Overlap only when all of one side is prefix+suffix.
        # In that case middle is empty on one side.
        if n == pre + suf:
            # A fully consumed by pre+suf means A is subsequence? Actually if n <= pre+suf then middle A empty
            # But suf was capped to n-pre, so n == pre+suf implies A middle empty
            mid = [2] * (m - pre - suf)
        elif m == pre + suf:
            mid = [1] * (n - pre - suf)
        else:
            # both non-empty but overlapping trim (should not happen due to cap)
            Am = A[pre:n - suf] if suf else A[pre:]
            Bm = B[pre:m - suf] if suf else B[pre:]
            mid = myers_core(Am, Bm)
    else:
        Am = A[pre:n - suf] if suf else A[pre:]
        Bm = B[pre:m - suf] if suf else B[pre:]
        # quick equal check on middles (rare)
        if Am == Bm:
            mid = [0] * len(Am)
        else:
            mid = myers_core(Am, Bm)
    if pre == 0 and suf == 0:
        tags = mid
    elif pre == 0:
        tags = mid + [0] * suf
    elif suf == 0:
        tags = [0] * pre + mid
    else:
        tags = [0] * pre + mid + [0] * suf
    # reorder each hunk: dels before inss
    # in-place reorder to avoid extra pass? do single pass building new list
    out = []
    ap = out.append
    i = 0
    L = len(tags)
    while i < L:
        t = tags[i]
        if t == 0:
            ap(0)
            i += 1
        else:
            j = i
            while j < L and tags[j] != 0:
                j += 1
            # block tags[i:j]: emit 1s then 2s
            # two passes over block (blocks are small usually)
            for k in range(i, j):
                if tags[k] == 1:
                    ap(1)
            for k in range(i, j):
                if tags[k] == 2:
                    ap(2)
            i = j
    return out


def indices_to_str(idxs):
    if not idxs:
        return "."
    parts = []
    start = idxs[0]
    prev = start
    for v in idxs[1:]:
        if v == prev + 1:
            prev = v
        else:
            parts.append(str(start) + "-" + str(prev + 1))
            start = v
            prev = v
    parts.append(str(start) + "-" + str(prev + 1))
    return ",".join(parts)


def char_ranges(old_bytes, new_bytes):
    try:
        os_ = old_bytes.decode("utf-8")
    except UnicodeDecodeError:
        os_ = old_bytes.decode("utf-8", errors="surrogateescape")
    try:
        ns = new_bytes.decode("utf-8")
    except UnicodeDecodeError:
        ns = new_bytes.decode("utf-8", errors="surrogateescape")
    if os_ == ns:
        return ".", "."
    tags = diff_tags(os_, ns)
    del_idx = []
    ins_idx = []
    oi = 0
    ni = 0
    for t in tags:
        if t == 0:
            oi += 1
            ni += 1
        elif t == 1:
            del_idx.append(oi)
            oi += 1
        else:
            ins_idx.append(ni)
            ni += 1
    return indices_to_str(del_idx), indices_to_str(ins_idx)


def main():
    if len(sys.argv) != 4 or sys.argv[1] not in ("lines", "highlight"):
        print("usage: main.py lines|highlight A_PATH B_PATH", file=sys.stderr)
        return 2
    command, a_path, b_path = sys.argv[1:]
    try:
        a_lines = read_lines(a_path)
        b_lines = read_lines(b_path)
    except OSError as e:
        print("error: cannot read file: " + str(e), file=sys.stderr)
        return 2
    A, B = map_ids(a_lines, b_lines)
    tags = diff_tags(A, B)
    out = sys.stdout.buffer
    if command == "lines":
        chunks = []
        ai = 0
        bi = 0
        for t in tags:
            if t == 0:
                chunks.append(b" " + a_lines[ai] + b"\n")
                ai += 1
                bi += 1
            elif t == 1:
                chunks.append(b"-" + a_lines[ai] + b"\n")
                ai += 1
            else:
                chunks.append(b"+" + b_lines[bi] + b"\n")
                bi += 1
        if chunks:
            out.write(b"".join(chunks))
        return 0
    else:
        chunks = []
        ai = 0
        bi = 0
        i = 0
        L = len(tags)
        while i < L:
            t = tags[i]
            if t == 0:
                chunks.append(b" " + a_lines[ai] + b"\n")
                ai += 1
                bi += 1
                i += 1
            else:
                j = i
                while j < L and tags[j] != 0:
                    j += 1
                # count dels (tags reordered: 1s then 2s)
                nd = 0
                for k in range(i, j):
                    if tags[k] == 1:
                        nd += 1
                ni_ = (j - i) - nd
                del_lines = a_lines[ai:ai + nd]
                ins_lines = b_lines[bi:bi + ni_]
                for dl in del_lines:
                    chunks.append(b"-" + dl + b"\n")
                ai += nd
                for idx, il in enumerate(ins_lines):
                    chunks.append(b"+" + il + b"\n")
                    if idx < nd:
                        ro, rn = char_ranges(del_lines[idx], il)
                        chunks.append(b"? " + ro.encode("ascii") + b" | " + rn.encode("ascii") + b"\n")
                bi += ni_
                i = j
        if chunks:
            out.write(b"".join(chunks))
        return 0


raise SystemExit(main())
