type fun_t<T> is function(T)->(int)

function id(int x) -> (int r):
    return x

public export method test():
    function(int|bool)->(int) fn1 = &id
    fun_t<int> fn2 = &id
    fun_t<int|bool> fn3 = fn2
    assume fn1(false) == 0
    assume fn3(false) == 0
