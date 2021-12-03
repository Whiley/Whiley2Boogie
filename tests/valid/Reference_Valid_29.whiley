// Reverse a linked list
type LinkedList<T> is null | &{ T data, LinkedList<T> next }

property equiv<T>(LinkedList<T> l, int i, T[] items) -> (bool r):
    (i < |items| && !(l is null) && l->data == items[i] && equiv(l->next,i+1,items)) ||
    (i == |items| && l == null)

method reverse<T>(LinkedList<T> v) -> (LinkedList<T> r):
    //
    LinkedList<T> w = null
    //
    while !(v is null):
        LinkedList<T> t = v->next
        v->next = w
        w = v
        v = t
    //
    return w

public export method test():
    LinkedList<int> l1 = null
    LinkedList<int> l2 = new { data: 2, next: l1 }
    LinkedList<int> l3 = new { data: 3, next: l2 }
    // Sanity check
    assert equiv(l3,0,[3,2])
    // Apply the reverse
    LinkedList<int> l4 = reverse(l3)
    // Assert reversal
    assert equiv(l4,0,[2,3])
