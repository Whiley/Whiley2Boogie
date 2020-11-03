public method main(int x) -> int
requires  x >= 0:
    //
    while x < 10:
        if x == 8:
            break
        x = x + 1
    //
    return x