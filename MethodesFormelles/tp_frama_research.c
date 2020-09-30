#include <stdio.h>
/*@
    requires \valid(a+ (0..(n-1)));
    requires n >= 0;

    behavior found:
    assumes n > 0;
    ensures 0 <= \result < n;
    ensures a[\result] == v;
    ensures \forall integer k; (\result <= k < n) ==> (a[k] != v);

    behavior not_found:
    assumes n > 0;
    ensures \result == n;
    ensures \forall integer k; (0 <= k < n) ==> (a[k] != v);

    complete behaviors found, not_found;
    disjoint behaviors found, not_found; 
*/
int find(const int *a, int n, int v)
{
    /*@
        loop assigns i;
        loop invariant 0 <= i <= n;
        loop invariant \forall integer k; (0 <= k < i) ==> (a[k] != a[i]);
        loop variant n-i;
    */
    for (int i = 0; i < n; i++)
    {
        if (a[i] == v)
        {
            return i;
        }
    }
    return n;
}

int main()
{
    int a[] = {13, 20, 4, 18, 13};
    int result = find(a, n, 13);
    if (result == n)
    {
        printf("13 not found\n");
    }
    else
    {
        printf("13 found, index = %d\n", result);
    }
    result = find(a, n, 21);
    if (result == n)
    {
        printf("21 not found\n");
    }
    else
    {
        printf("21 found, index = %d\n", result);
    }
}