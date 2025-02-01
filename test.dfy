method Add(a: int, b: int) returns (result: int)
  ensures result == a + b // postcondition : résultat est la somme de a et b
{
  result := a + b;
}

method Sum(n: nat) returns (res: nat)
  ensures res == n * (n + 1) / 2 // postcondition : résultat est la somme des n premiers entiers
{
  var i := 0;
  res := 0;

  while i < n
    invariant 0 <= i <= n 
    invariant res == i * (i + 1) / 2 
  {
    res := res + i;
    i := i + 1;
  }
}

method Main()
{
  var a: int := 1;
  var b: int := 2;
  var c: int := Add(a, b);
  assert c == 3; // vérifie que c est bien égal à 3
  print c,"\n";
  var d: int := Sum(10);
  assert d == 55; // vérifie que d est bien égal à 55
  print d,"\n";
}