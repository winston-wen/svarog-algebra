def delta(a, b, c):
    return b**2 - 4 * a * c


def solve_c(a, b):
    num = b**2 + 599
    den = 4 * a
    if num % den != 0:
        return None
    else:
        return num // den


def find_form(b):
    assert b % 2 == 1
    a = 0
    c = None
    lim = abs(b) * 10
    res = []
    while a < lim:
        a += 1
        c = solve_c(a, b)
        if c != None:
            res.append((a, b, c))
    return res


if __name__ == "__main__":
    forms = find_form(b=-893)
    for form in forms:
        print(*form)
