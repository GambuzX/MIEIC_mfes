// Checks if array 'a' is sorted between positions 'from' (inclusive) and 'to' (exclusive).
predicate isSorted(a: array<int>, from: nat, to: nat) 
    requires 0 <= from <= to <= a.Length
    reads a
{
    forall i, j :: from <= i < j < to ==> a[i] <= a[j]
}

// Sorts array 'a' using the insertion sort algorithm.
method insertionSort(a: array<int>) 
    modifies a
    ensures isSorted(a, 0, a.Length)
    ensures multiset(a[..]) == multiset(old(a[..]))
{
    var i := 0;
    while i < a.Length 
        decreases a.Length - i
        invariant 0 <= i <= a.Length
        invariant isSorted(a, 0, i)
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
        var j := i;
        while j > 0 && a[j-1] > a[j] 
            decreases j
            invariant 0 <= j <= i <= a.Length
            invariant forall l, r :: 0 <= l < r <= i ==> if r != j then a[l] <= a[r] else true
            invariant multiset(a[..]) == multiset(old(a[..]))
        {
            a[j-1], a[j] := a[j], a[j-1];
            j := j - 1;
        }
        i := i + 1;
    }
}


// Simple test case to check the postcondition
method testInsertionSort() {
  var a := new int[] [ 9, 4, 3, 6, 8];
  assert a[..] == [9, 4, 3, 6, 8];
  insertionSort(a);
  assert a[..] == [3, 4, 6, 8, 9];
}

/*
a) Identify adequate pre and post-conditions for this method, and encode them 
as “requires” and “ensures” clauses in Dafny. (Suggestion: See SelectionSort.dfy).

b) Identify adequate variants and invariants for the two loops, and encode them as 
“decreases” and “invariant” clauses in Dafny.

*/
