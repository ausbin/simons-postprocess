I am working on converting the proof below into Coq.
This approach is heavily inspired by a post by Tristan Nemoz[1].

[1]: https://quantumcomputing.stackexchange.com/a/29407/13156)

------------------------------------------------------------------------------

(In the following discussion, indices are assumed to begin at 1, not 0.
 Note this differs from numpy, where indices begin at 0.)

Definition 1: A **n-fold Simon matrix** is a (n-1)xn matrix in reduced
              row echelon form containing only 0 and 1 entries and
              without any rows of all zeros.

The input to this function (mat) is a Simon matrix. The n variables in
the system of equations are exactly the n bits of a secret string s,
which cannot consist of all 0s.

Definition 2: The **special column** of a n-fold Simon matrix M is the
              column whose index is the smallest 1 <= c <= n such that
              either c = n or M[c,c] = 0.

Lemma 3: Suppose M is an n-fold Simon matrix whose special column has
         index c. Then if c <= i < n and 1 <= j <= n,
                  { 1  if j = i+1
         M[i,j] = {
                  { 0  otherwise
Proof:
Suppose c < n, since otherwise the statement of the lemma is not
applicable. By definition of special column, M[k,k] = 1 for all
1 <= k < c, yet M[c,c] = 0. By definition of Simon matrix, however, the
row at index c cannot consist of all zeros. Thus, there must be an entry
M[c,l] = 1 with c < l <= n-1. Yet for each c < j <= n-1, the row with
index j must also have a nonzero by definition of Simon matrix. In order
not to violate the definition of reduced row echelon form, then, l=c+1
and M[j,m] = 1 if m=j+1 and 0 otherwise for all j. Qed.


Lemma 4: Suppose M is an n-fold Simon matrix whose special column has
         index c. Then every row 1 <= i < c consists of zeros except for
         a leading entry in column i and possibly a 1 in column c.
Proof:
By definition of special column, M[i,i] = 1 for all i, since i < c. Then
for all 1 <= k_i < i, M[i, k_i] = 0 by definition of row echelon form, and
for all i < l_i < c, M[i, l_i] = 0 by definition of reduced row echelon
form. And by Lemma 3 and the definition of reduced row echelon form, for
all c < h_i <= n, M[i, h_i] = 0. Thus, M[i,c] is the only possible other
1 in row i besides the leading entry M[i,i]. Qed.


Theorem: If M is an n-fold Simon matrix and its special column is at
         index c, then the n-bit secret string is
         M[1,c],M[2,c],...,M[c-1,c],1,0,0,...,0.
Proof:
Lemma 3 implies there are equations s_i' = 0 (mod 2) with c < i' <= n.
Thus, the last n-c bits of the secret string are 0.

By Lemma 4, each row at index i' such that 1 <= i < c represents an
equation s_i + M[i,c]*s_c = 0 (mod 2).

Now, for the purpose of contradiction, assume that s_c = 0. If s_c = 0,
though, each aforementioned equation becomes s_i = 0 (mod 2), so the
first c-1 bits of the secret string are 0. However, if the first c-1 bits
of the secret string are 0, and bit c of the secret string is zero (since
s_c=0), and the last n-c bits of the secret string are 0, then the secret
string s must consist of all 0s. This contradicts the assumption that s
does not consist of all zeros, so we must conclude that s_c = 1.

Consequently, each aforementioned equation is equivalent to
s_i + M[i,c] = 0 (mod 2), which is equivalent to s_i = M[i,c] (mod 2). In
other words, the first c-1 bits of the secret string are the first c-1
elements of column c of M. The next bit is 1 (since we proved that
s_c=1), and the remaining n-c bits are zeros as initially shown. Qed.
