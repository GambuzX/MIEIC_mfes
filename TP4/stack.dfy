type T = int // to allow doing new T[capacity], but can be other type 
 
class {:autocontracts} Stack
{
    const elems: array<T>; // immutable (pointer)
    var size : nat; // used size

    predicate Valid()
    reads this {
        size <= elems.Length
    }
 
    constructor (capacity: nat)
    requires capacity > 0
    ensures size == 0
    ensures elems.Length == capacity
    {
        elems := new T[capacity];
        size := 0; 
    }
 
    predicate method isEmpty()
    {
        size == 0
    }
 
    predicate method isFull()
    {
        size == elems.Length
    }
 
    method push(x : T)
    requires size < elems.Length

    ensures size == old(size)+1
    ensures elems[old(size)] == x
    ensures forall i :: 0 <= i < old(size) ==> elems[i] == old(elems)[i]
    
    // mais compacto 
    //ensures elems[..size] == old(elems[..size]) + [x]
    {
        elems[size] := x;
        size := size + 1;
    }
 
    function method top(): T
    requires 0 < size <= elems.Length
    {
         elems[size-1]
    }
    
    method pop() 
    requires size > 0
    ensures elems[..size] == old(elems[..size-1])
    {
         size := size-1;
    }
}
 
// A simple test case.
method {:verify false} Main()
{
    var s := new Stack(3);
    assert s.isEmpty();
    s.push(1);
    s.push(2);
    s.push(3);
    assert s.top() == 3;
    assert s.isFull();
    s.pop();
    assert s.top() == 2;
    print "top = ", s.top(), " \n";
}

/*
a) Compile and run this program and check that the correct result is printed.
b) Add a class invariant (predicate Valid()) to check the validity of the fields values, i.e., that the size of the stack does not exceed the allocated capacity. Add the {:autocontracts} attribute after the “class” keyword, so that Dafny checks automatically the class invariant before & after all methods.
c) Add relevant pre-conditions to methods, constructors, functions, and predicates, and remove the “{:verify false}” attribute. 
d) Add post-conditions to methods and constructors describing their intended effect. Notice that functions and predicates don’t need post-conditions. At this point, the assertions in the test scenario should be checked successfully by Dafny.

*/