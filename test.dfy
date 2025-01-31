method Add(a: int, b: int) returns (result: int)
  ensures result == a + b // précondition : résultat est la somme de a et b
{
  result := a + b;
}

method Sum(n: int) returns (result: int)
  requires n >= 0
  ensures result == n * (n + 1) / 2
{
  var i := 0;
  var sum := 0;
  while i < n
    invariant 0 <= i <= n && sum == (i * (i + 1)) / 2
  {
    sum := sum + i;
    i := i + 1;
  }
  result := sum;
}

method Main()
{
  var a: int := 1;
  var b: int := 2;
  var c: int := Add(a, b);
  assert c == 3; // vérifie que c est bien égal à 3
  var d: int := Sum(10);
  assert d == 55; // vérifie que d est bien égal à 55
}