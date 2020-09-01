predicate sorted (a : seq<int>)
{
    forall j, k :: 0 <= j < k < |a| ==> a[j] <= a[k]
}

predicate nodups (a : seq<int>)
{
    forall i, j :: 0 <= i < |a| ==> 0 <= j < |a| ==> a[i] == a[j] ==> i == j
}

method removeDups(a : seq<int>) returns (b:seq<int>)
    requires sorted(a)
    ensures nodups(b)
{
    var indexb : int;
    var a' : seq<int>;
    indexb := 1;
    a' := [];

    if( |a| <= 1) 
    {
        return a;
    }

    while (indexb < |a|)
    invariant 0 <= indexb - 1 < |a|;
    invariant(sorted(a[0..(indexb)]))
    invariant(sorted(a))
    invariant(|a| > indexb - 1 ==> sorted(a' + [a[indexb - 1]]))
    invariant(|a'| > 0 ==> a'[|a'| - 1] <= a[indexb - 1])
    invariant(sorted(a'))
    invariant(|a| > indexb - 1 ==> nodups(a' + [a[indexb - 1]]))
    invariant(nodups(a'))
    {
        if(a[indexb] != a[indexb - 1])
        {
// i originally had these invariants, but it appears they are unnecessary            
//            assert (a[indexb] > a[indexb - 1]);
//            assert (indexb - 1 < |a|);
            a' := (a' + [a[indexb - 1]]);
        }
        indexb := indexb + 1;
    }
    return a';
}