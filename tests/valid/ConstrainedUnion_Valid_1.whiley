

type nat is (int x) where x >= 0

method f(bool|int v) -> (int r)
ensures r >= 0:
    //
    if v is bool|nat:
        return 1
    //
    return 0

public export method test():
    int result = f(1)
    assume result == 1
    //
    result = f(true)
    assume result == 1
    //
    result = f(-1)
    assume result == 0
