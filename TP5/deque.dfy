type T = int // for demo purposes, but could be another type
 
class {:autocontracts} Deque {
    // (Private) concrete state variables 
    const list: array<T>; // circular array, from list[start] (front) to list[(start+size-1) % list.Length] (back) 
    var start : nat; 
    var size : nat;

    ghost var elems: seq<T>;  // front at head, back at tail
    ghost const capacity: nat; 

    predicate Valid() {
        size <= list.Length &&
        0 <= start < list.Length &&

        capacity == list.Length &&
        |elems| == size &&
        //forall i :: 0 <= i < size ==> list[(start+i) % list.Length] == elems[i] &&
        elems == (list[..] + list[..])[start .. start+size]
    }

    constructor (capacity: nat) 
        requires capacity > 0
        ensures elems == []
        ensures this.capacity == capacity
    {
        list := new T[capacity];
        start := 0;
        size := 0;

        this.elems := [];
        this.capacity := capacity;
    }
 
    predicate method isEmpty() 
        ensures isEmpty() <==> elems == []
    {
        size == 0
    }
    
    predicate method isFull()
        ensures isFull() <==> |elems| == capacity
    {
        size == list.Length
    }
 
    function method front() : T 
        requires !isEmpty()
        ensures front() == elems[0]
    {
        list[start]
    }
 
    function method back() : T 
        requires !isEmpty()
        ensures back() == elems[|elems|-1]
    {
        list[(start + size - 1) % list.Length] 
    }
    
    method push_back(x : T) 
        requires !isFull()
        ensures elems == old(elems) + [x]
        ensures elems == (list[..] + list[..])[start .. start+size]
    {
        list[(start + size) % list.Length] := x;
        size := size + 1;
        elems := elems + [x];
    }
 
    method pop_back() 
        requires |elems| > 0
        ensures elems == old(elems)[..(|old(elems)|-1)]
    {
        size := size - 1;
        elems := elems[..size];
    }
 
    method push_front(x : T) 
        requires !isFull()
        ensures elems == [x] + old(elems)
        ensures |elems| <= capacity
    {
        if start > 0 {
            start := start - 1;
        }
        else {
            start := list.Length - 1;
        }
        list[start] := x;
        size := size + 1;

        elems := [x] + elems;
    }    
 
    method pop_front() 
        requires !isEmpty()
        ensures elems == old(elems)[1..]
    {
        if start + 1 < list.Length {
            start := start + 1;
        }
        else {
            start := 0;
        }
        size := size - 1;
        elems := elems[1..];
    } 
}
 
// A simple test scenario.
method testDeque()
{
    var q := new Deque(3);
    assert q.isEmpty();
    q.push_front(1);
    assert q.front() == 1;
    assert q.back() == 1;
    q.push_front(2);
    assert q.front() == 2;
    assert q.back() == 1;
    q.push_back(3);
    assert q.front() == 2;
    assert q.back() == 3;
    assert q.isFull();
    q.pop_back();
    assert q.front() == 2;
    assert q.back() == 1;
    q.pop_front();
    assert q.front() == 1;
    assert q.back() == 1;
    q.pop_front();
    assert q.isEmpty();
}

/*

a) Add the following ghost fields to describe the state of the Deque in an abstract way (independently of the internal state representation):
    // (Public) ghost variables used for specification purposes only
    ghost var elems: seq<T>;  // front at head, back at tail
    ghost const capacity: nat; 

b) Add a class invariant (predicate Valid()) to ensure: (i) the consistency of the concrete state variables; (ii) the consistency between the concrete and abstract (ghost) state variables (abstraction relation).

c) Add relevant pre- and post conditions to all methods, constructors, functions, and predicates, based on the abstract state variables only. You also need to add instructions to update the abstract state variables in the body of constructors and methods.

d) Check is all test assertions are successfully checked by Dafny and fix any problems found.


e) Redo with a state abstraction function instead of a ghost variable.


*/