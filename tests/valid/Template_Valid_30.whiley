type nat is (int x) where x >= 0
type State<T> is { T[] items }

function f(State<nat> xs, nat i) -> (nat r)
requires i < |xs.items|
ensures r == xs.items[i]:
    //
    return xs.items[i]

public export method test():
    State<nat> s = { items: [1,2,3] }    
    //
    assert f(s,0) == 1
    assert f(s,1) == 2
    assert f(s,2) == 3
    