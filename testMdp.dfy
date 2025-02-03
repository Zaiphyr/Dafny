method CheckPassword(password: string) returns (isValid: bool)
    ensures isValid ==> |password| >= 8 &&
                        (exists i :: 0 <= i < |password| && 'A' <= password[i] <= 'Z') &&
                        (exists i :: 0 <= i < |password| && '0' <= password[i] <= '9') &&
                        (exists i :: 0 <= i < |password| && password[i] in {'@', '#', '$', '%', '&', '*', '!', '?'})
{
    var hasUpper := false;
    var hasDigit := false;
    var hasSpecial := false;

    var i := 0;
    while i < |password|
        decreases |password| - i
        invariant 0 <= i <= |password|
        invariant hasUpper ==> (exists j :: 0 <= j < i && 'A' <= password[j] <= 'Z')
        invariant hasDigit ==> (exists j :: 0 <= j < i && '0' <= password[j] <= '9')
        invariant hasSpecial ==> (exists j :: 0 <= j < i && password[j] in {'@', '#', '$', '%', '&', '*', '!', '?'})
    {
        if 'A' <= password[i] <= 'Z' {
            hasUpper := true;
        }
        if '0' <= password[i] <= '9' {
            hasDigit := true;
        }
        if password[i] in {'@', '#', '$', '%', '&', '*', '!', '?'} {
            hasSpecial := true;
        }
        i := i + 1;
    }

    isValid := |password| >= 8 && hasUpper && hasDigit && hasSpecial;
}
