From Coq Require Import Lia.
From Coq Require Import ssreflect ssrbool.
Theorem t:
    forall n: nat, 1 + n > n.
Proof.
  intro n.
  lia.
Qed.

Lemma addnC n m : n + m = m + n.
Proof. by elim: n => //= ? ->. Qed.

Lemma addnAC n m l : n + m + l = m + (n + l).
Proof.
  by elim : n => //= ? ->.
Qed.