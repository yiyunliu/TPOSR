Require Export syntax imports.

Definition context := list tm.

Inductive lookup : nat -> context -> tm -> Prop :=
  | here : forall {A Γ}, lookup 0 (A :: Γ) (A ⟨shift⟩)
  | there : forall {n A Γ B},
      lookup n Γ A -> lookup (S n) (B :: Γ) (A ⟨shift⟩).

Definition lookup_good_renaming ξ Γ Δ :=
  forall i A, lookup i Γ A -> lookup (ξ i) Δ A⟨ξ⟩.

Derive Inversion lookup_inv with (forall i Γ A, lookup i Γ A).

Reserved Notation "Γ ⊢ a ▻ b ∈ B ⇒ A" (at level 70, no associativity).
Reserved Notation "Γ ⊢ a ▻+ b ∈ A" (at level 70, no associativity).
Reserved Notation "⊢ Γ" (at level 70, no associativity).

Inductive WtRed : context -> tm -> tm -> tm -> tm -> Prop :=
| WR_Var Γ n A :
  ⊢ Γ ->
  lookup n Γ A ->
  (* ------------- *)
  Γ ⊢ var_tm n ▻ var_tm n ∈ A ⇒ A

| WR_Univ Γ i :
  ⊢ Γ ->
  (* ----------- *)
  Γ ⊢ Univ i ▻ Univ i ∈ Univ (S i) ⇒ Univ (S i)

| WR_Prod Γ i _A _B A A' B B' :
  Γ ⊢ A ▻ A' ∈ _A ⇒ Univ i ->
  A :: Γ ⊢ B ▻ B' ∈ _B ⇒ Univ i ->
  (* ------------------- *)
  Γ ⊢ Pi A B ▻ Pi A' B' ∈ Univ i ⇒ Univ i

| WR_Lam Γ _A A A' i _B B _M M M' :
  Γ ⊢ A ▻ A' ∈ _A ⇒ Univ i ->
  A :: Γ ⊢ B ▻ B ∈ _B ⇒ Univ i ->
  A :: Γ ⊢ M ▻ M' ∈ _M ⇒ B ->
  (* ------------------ *)
  Γ ⊢ Lam A M ▻ Lam A' M' ∈ Pi A B ⇒ Pi A B

| WR_App Γ _A A A' i _B  B B' _M M M' _N N N' :
  Γ ⊢ A ▻ A' ∈ _A ⇒ Univ i ->
  A :: Γ ⊢ B ▻ B' ∈ _B ⇒ Univ i ->
  Γ ⊢ M ▻ M' ∈ _M ⇒ Pi A B ->
  Γ ⊢ N ▻ N' ∈ _N ⇒ A ->
  (* ------------------------ *)
  Γ ⊢ App A B M N ▻ App A' B' M' N' ∈ B[N..] ⇒ B[N..]

| WR_Beta Γ i (A _A A' _A' A0 B _B M M' _M N N' _N : tm):
  Γ ⊢ A ▻ A ∈ _A ⇒ Univ i ->
  Γ ⊢ A' ▻ A' ∈ _A' ⇒ Univ i ->
  Γ ⊢ A0 ▻+ A ∈ Univ i ->
  Γ ⊢ A0 ▻+ A' ∈ Univ i ->
  A :: Γ ⊢ B ▻ B ∈ _B ⇒ Univ i ->
  A :: Γ ⊢ M ▻ M' ∈ _M ⇒ B ->
  Γ ⊢ N ▻ N' ∈ _N ⇒ A ->
  (*----------------------  *)
  Γ ⊢ App A' B (Lam A M) N ▻ M'[N'..] ∈ B[N..] ⇒ B[N..]

| WR_TyUnit Γ i :
  ⊢ Γ ->
  (* ----------- *)
  Γ ⊢ TyUnit ▻ TyUnit ∈ Univ i ⇒ Univ i

| WR_TmUnit Γ :
  ⊢ Γ ->
  (* ----------- *)
  Γ ⊢ TmUnit ▻ TmUnit ∈ TyUnit ⇒ TyUnit

| WR_TmUnitEta Γ A i a b :
  Γ ⊢ a ▻ b ∈ A ⇒ TyUnit ->
  Γ ⊢ A ▻+ TyUnit ∈ Univ i ->
  (* ----------- *)
  Γ ⊢ a ▻ TmUnit ∈ A ⇒ TyUnit

| WR_Red Γ M N TM _A A B i :
  Γ ⊢ M ▻ N ∈ TM ⇒ A ->
  Γ ⊢ A ▻ B ∈ _A ⇒ Univ i ->
  (* ----------------- *)
  Γ ⊢ M ▻ N ∈ TM ⇒ B

| WR_Exp Γ M N TM _B A B i :
  Γ ⊢ M ▻ N ∈ TM ⇒ A ->
  Γ ⊢ B ▻ A ∈ _B ⇒ Univ i ->
  (* ----------------- *)
  Γ ⊢ M ▻ N ∈ TM ⇒ B

with Wf : context -> Prop :=
| Wf_nil :
  (* -------- *)
  ⊢ nil
| Wf_cons Γ A B _A i :
  Γ ⊢ A ▻ B ∈ _A ⇒ Univ i ->
  (* ---------- *)
  ⊢ A :: Γ

with WtReds : context -> tm -> tm -> tm -> Prop :=
| WRs_One Γ M N _M A:
  Γ ⊢ M ▻ N ∈ _M ⇒ A ->
  (* ------------- *)
  Γ ⊢ M ▻+ N ∈ A

| WRs_Trans Γ M N _M P A:
  Γ ⊢ M ▻ N ∈ _M ⇒ A ->
  Γ ⊢ N ▻+ P ∈ A ->
  (* ------------- *)
  Γ ⊢ M ▻+ P ∈ A
where
"Γ ⊢ a ▻ b ∈ B ⇒ A" := (WtRed Γ a b B A)
and "⊢ Γ" := (Wf Γ)
and "Γ ⊢ a ▻+ b ∈ A" := (WtReds Γ a b A).

Reserved Notation "Γ ⊢ A ≡ B" (at level 70, no associativity).
Inductive WtEquiv Γ : tm -> tm -> Prop :=
| WE_Red A B _A i :
  Γ ⊢ A ▻ B ∈ _A ⇒ Univ i ->
  (* ------------------- *)
  Γ ⊢ A ≡ B
| WE_Exp A B i _B :
  Γ ⊢ B ▻ A ∈ _B ⇒ Univ i ->
  (* ------------------- *)
  Γ ⊢ A ≡ B
| WE_Trans A B C :
  Γ ⊢ A ≡ B ->
  Γ ⊢ B ≡ C ->
  Γ ⊢ A ≡ C
where
"Γ ⊢ A ≡ B" := (WtEquiv Γ A B).

#[export]Hint Constructors WtEquiv WtReds WtRed Wf : wt.

Lemma Equiv_sym Γ A B (h : Γ ⊢ A ≡ B) : Γ ⊢ B ≡ A.
Proof. elim : A B / h; eauto with wt. Qed.

Scheme red_ind := Induction for WtRed Sort Prop
    with reds_ind := Induction for WtReds Sort Prop
    with wf_ind := Induction for Wf Sort Prop.

Combined Scheme wt_mutual_ind from red_ind, reds_ind, wf_ind.
