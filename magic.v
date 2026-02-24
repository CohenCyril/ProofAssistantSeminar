Add Search Blacklist "Unnamed" "Nat" "Hexadecimal" "Decimal" "plus" "mult".
Remove Hints plus_n_O plus_n_Sm mult_n_O mult_n_Sm : core.

Lemma add0n n : 0 + n = n.
Proof. reflexivity. Qed.

Lemma addSn n m : S n + m = S (n + m).
Proof. reflexivity. Qed.

Lemma mul0n n : 0 * n = 0.
Proof. reflexivity. Qed.

Lemma mulSn n m : S n * m = m + n * m.
Proof. reflexivity. Qed.

