#include <stdio.h>
/*@
    requires \valid(a+ (0..(n-1)));
    requires n >= 0;

    assigns \nothing;

    behavior empty:
    assumes n==0;
    ensures \result==0;

    behavior not_empty:
    assumes n > 0;
    ensures 0 <= \result < n;
    ensures \forall integer k; (0 <= k < n) ==> (a[k] >= a[\result]);
    ensures \forall integer k; (0 <= k < \result) ==> (a[k] > a[\result]);

    complete behaviors empty, not_empty;
    disjoint behaviors empty, not_empty;
*/
int min_element(const int *a, int n)
{
    if (n == 0)
    {
        return 0;
    }
    int min = 0;
    /*@ loop assigns i, min;
        loop invariant 0 <= i <= n;
        loop invariant 0 <= min < n;
        loop invariant 0 <= min <= i;
        loop invariant \forall integer k; (0 <= k < min) ==> (a[k] > a[min]);
        loop invariant \forall integer k; (0 <= k < i) ==> (a[k] >= a[min]);
        loop variant n-i+1;
    */
    for (int i = 1; i < n; i++)
    {
        if (a[min] > a[i])
        {
            min = i;
        }
    }
    return min;
};

int main()
{
    int a[] = {1, 2, 6, -4, 3};
    printf("min = %d, index = %d\n", a[min_element(a, 5)], min_element(a, 5));
    return 0;
}