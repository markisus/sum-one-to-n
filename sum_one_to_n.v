Require Coq.Arith.PeanoNat.
Require Import Arith Omega.

Fixpoint sum_one_to_n (n : nat) : nat :=
  match n with
  | 0 => 0
  | S p => (S p) + (sum_one_to_n p)
  end.

Lemma plus_one_both_sides : forall a b : nat,
    a = b <-> S a = S b.
Proof.
  intros a b.
  split; intros.
  - rewrite H.
    reflexivity.
  - inversion H.
    reflexivity.
Qed.

Lemma sn_eq_plus_n_1 : forall n : nat,
    S n = n + 1.
Proof.
  intros n.
  rewrite PeanoNat.Nat.add_comm.
  reflexivity.
Qed.

Lemma mul_sn_m_eq : forall n m : nat,
    (S n) * m = n*m + m.
Proof.
  intros n m.
  simpl.
  omega.
Qed.

Theorem sum_one_to_n_reduction :
  forall n : nat,
    2 * (sum_one_to_n n) = (n + 1) * n.
Proof.
  induction n.
  (* base case *)
  - reflexivity.
  - simpl.
    rewrite <- plus_one_both_sides.
    simpl in IHn.
    rewrite <- plus_n_O in IHn.
    rewrite <- plus_n_O.
    rewrite sn_eq_plus_n_1.
    rewrite -> PeanoNat.Nat.add_assoc.
    rewrite -> PeanoNat.Nat.add_assoc.
    rewrite <- sn_eq_plus_n_1.
    rewrite <- (PeanoNat.Nat.add_assoc n (sum_one_to_n n) n).
    rewrite <- (PeanoNat.Nat.add_assoc n (sum_one_to_n n + n) (sum_one_to_n n)).
    rewrite <- (PeanoNat.Nat.add_assoc (sum_one_to_n n) n (sum_one_to_n n)).
    rewrite  (PeanoNat.Nat.add_comm n (sum_one_to_n n)).
    rewrite -> (PeanoNat.Nat.add_assoc (sum_one_to_n n) (sum_one_to_n n) n).
    rewrite IHn.
    rewrite <- sn_eq_plus_n_1.
    simpl.
    rewrite <- plus_n_Sm.
    rewrite <- plus_one_both_sides.
    rewrite (Nat.mul_comm n (S n)).
    simpl.
    omega.
Qed.

Theorem sum_one_to_n_reduction' :
  forall n : nat,
    2 * (sum_one_to_n n) = (n + 1) * n.
Proof.
  induction n.
  (* base case *)
  - reflexivity.
  (* inductive *)
  - simpl.
    assert (eq : n + sum_one_to_n n + S (n + sum_one_to_n n + 0) =
            sum_one_to_n n + (sum_one_to_n n) + n + n + 1).
    { omega. }
    rewrite eq.
    simpl in IHn.
    rewrite <- plus_n_O in IHn.
    rewrite IHn.
    simpl.
    assert (eq' : n + 1 = S n).
    { omega. }
    rewrite eq'.
    simpl.
    rewrite (Nat.mul_comm (n) (S n)).
    simpl.
    omega.
Qed.
