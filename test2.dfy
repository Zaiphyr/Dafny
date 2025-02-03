ghost method Sum(n: nat) returns (result: nat)
    ensures result == n * (n + 1) / 2
{
    var sum := 0;
    var i := 0;
    
    while i <= n
        invariant sum == (i * (i - 1)) / 2
        invariant 0 <= i <= n + 1
        decreases n - i
    {
        sum := sum + i;
        i := i + 1;
    }
    
    result := sum;
assert result == n * (n + 1) / 2;
}

ghost method TestSum()
{
    var n: nat := 10;
    var result := Sum(n);
    
    assert result == 10 * (10 + 1) / 2; // Vérification formelle
}

method Example(n: int) 
{
    var i := 0;
    while true 
      decreases n - i // Preuve que i s'approche de n
    {
        if i >= n {
            break;
        }
        i := i + 1;
    }
}