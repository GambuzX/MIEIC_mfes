function P(n: nat): nat { if n <= 2 then 1 else P(n-2) + P(n-3) }

method calcP(n: nat) returns (res: nat)  
ensures res == P(n) {
    if n <= 2 { return 1; }
    var a, b, c := 1, 1, 1; // P(0), P(1), P(2)
    var i := 2;
    while i < n 
        decreases n-i
        invariant i <= n && c == P(i) && b == P(i-1) && a == P(i-2)
    {
        a, b, c := b, c, a + b;
        i := i + 1;
    }
    res := c;
}