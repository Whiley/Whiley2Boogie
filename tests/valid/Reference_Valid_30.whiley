public export method test():
    int i = 0
    &int q = new 1
    &int p = new 2
    //
    while i < 10:
        int x = *p
        *q = 1
        i = i + 1
    //
    assert *p == 2
