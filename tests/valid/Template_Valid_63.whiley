type Box<T> is { T next }

function init<T>(T item) -> (Box<T> p)
ensures p.next == item:
    return {next: item}

function create<T>(Box<T> item) -> (Box<Box<T> > p)
ensures p.next == item:
    return {next: item}

public export method test():
    assert init(1) == {next: 1}
    assert create(init(2)) == {next: {next: 2}}
    assert create(create(init(3))) == {next: {next: {next: 3}}}
