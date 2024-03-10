Require Export syntax imports.

Definition context := list tm.

Inductive lookup : nat -> context -> tm -> Prop :=
  | here : forall {A Γ}, lookup 0 (A :: Γ) (A ⟨shift⟩)
  | there : forall {n A Γ B},
      lookup n Γ A -> lookup (S n) (B :: Γ) (A ⟨shift⟩).

Definition lookup_good_renaming ξ Γ Δ :=
  forall i A, lookup i Γ A -> lookup (ξ i) Δ A⟨ξ⟩.

Derive Inversion lookup_inv with (forall i Γ A, lookup i Γ A).

Reserved Notation "Γ ⊢ a ▻ b ∈  A" (at level 70, no associativity).
Reserved Notation "Γ ⊢ a ▻+ b ∈  A" (at level 70, no associativity).
Reserved Notation "⊢ Γ" (at level 70, no associativity).

Inductive WtRed : context -> tm -> tm -> tm -> Prop :=
| WR_Var Γ n A :
  ⊢ Γ ->
  lookup n Γ A ->
  (* ------------- *)
  Γ ⊢ var_tm n ▻ var_tm n ∈ A

| WR_Univ Γ i :
  ⊢ Γ ->
  (* ----------- *)
  Γ ⊢ Univ i ▻ Univ i ∈ Univ (S i)

| WR_Prod Γ i A A' B B' :
  Γ ⊢ A ▻ A' ∈ Univ i ->
  A :: Γ ⊢ B ▻ B' ∈ Univ i ->
  (* ------------------- *)
  Γ ⊢ Pi A B ▻ Pi A' B' ∈ Univ i

| WR_Lam Γ A A' i B M M' :
  Γ ⊢ A ▻ A' ∈ Univ i ->
  A :: Γ ⊢ B ▻ B ∈ Univ i ->
  A :: Γ ⊢ M ▻ M' ∈ B ->
  (* ------------------ *)
  Γ ⊢ Lam A M ▻ Lam A' M' ∈ Pi A B

| WR_App Γ A A' i B B' M M' N N' :
  Γ ⊢ A ▻ A' ∈ Univ i ->
  A :: Γ ⊢ B ▻ B' ∈ Univ i ->
  Γ ⊢ M ▻ M' ∈ Pi A B ->
  Γ ⊢ N ▻ N' ∈ A ->
  (* ------------------------ *)
  Γ ⊢ App B M N ▻ App B' M' N' ∈ B[N..]

| WR_Beta Γ A i A' B M M' N N' :
  Γ ⊢ A ▻ A' ∈ Univ i ->
  A :: Γ ⊢ B ▻ B ∈ Univ i ->
  A :: Γ ⊢ M ▻ M' ∈ B ->
  Γ ⊢ N ▻ N' ∈ A ->
  (*----------------------  *)
  Γ ⊢ App B (Lam A M) N ▻ M'[N'..] ∈ B[N..]

| WR_TyUnit Γ :
  ⊢ Γ ->
  (* ----------- *)
  Γ ⊢ TyUnit ▻ TyUnit ∈ Univ 0

| WR_TmUnit Γ :
  ⊢ Γ ->
  (* ----------- *)
  Γ ⊢ TmUnit ▻ TmUnit ∈ TyUnit

| WR_TmUnitEta Γ a b :
  Γ ⊢ a ▻ b ∈ TyUnit ->
  (* ----------- *)
  Γ ⊢ a ▻ TmUnit ∈ TyUnit

| WR_Red Γ M N A B i :
  Γ ⊢ M ▻ N ∈ A ->
  Γ ⊢ A ▻ B ∈ Univ i ->
  (* ----------------- *)
  Γ ⊢ M ▻ N ∈ B

| WR_Exp Γ M N A B i :
  Γ ⊢ M ▻ N ∈ A ->
  Γ ⊢ B ▻ A ∈ Univ i ->
  (* ----------------- *)
  Γ ⊢ M ▻ N ∈ B

with Wf : context -> Prop :=
| Wf_nil :
  (* -------- *)
  ⊢ nil
| Wf_cons Γ A B i :
  Γ ⊢ A ▻ B ∈ Univ i ->
  (* ---------- *)
  ⊢ A :: Γ
where "Γ ⊢ a ▻ b ∈ A" := (WtRed Γ a b A)
and "⊢ Γ" := (Wf Γ).


Inductive WtReds Γ M N A : Prop :=
| WRs_One :
  Γ ⊢ M ▻ N ∈ A ->
  (* ------------- *)
  Γ ⊢ M ▻+ N ∈ A

| WRs_Trans P :
  Γ ⊢ M ▻ P ∈ A ->
  Γ ⊢ P ▻+ N ∈ A ->
  (* ------------- *)
  Γ ⊢ M ▻+ N ∈ A
where
 "Γ ⊢ a ▻+ b ∈ A" := (WtReds Γ a b A).

Reserved Notation "Γ ⊢ M ≡ N ∈ i" (at level 70, no associativity).
Inductive WtEquiv Γ M N i : Prop :=
| WE_Red :
  Γ ⊢ M ▻ N ∈ Univ i ->
  (* ------------------- *)
  Γ ⊢ M ≡ N ∈ i
| WE_Exp :
  Γ ⊢ N ▻ M ∈ Univ i ->
  (* ------------------- *)
  Γ ⊢ M ≡ N ∈ i
| WE_Trans P :
  Γ ⊢ M ≡ P ∈ i ->
  Γ ⊢ P ≡ N ∈ i ->
  (* ----------------- *)
  Γ ⊢ M ≡ N ∈ i
where
"Γ ⊢ A ≡ B ∈ i" := (WtEquiv Γ A B i).

#[export]Hint Constructors WtEquiv WtReds WtRed Wf : wt.

Lemma Equiv_sym Γ A B i (h : Γ ⊢ A ≡ B ∈ i) : Γ ⊢ B ≡ A ∈ i.
Proof. elim : h; eauto with wt. Qed.

#[export]Hint Resolve Equiv_sym : wt.

Scheme red_ind := Induction for WtRed Sort Prop
    with wf_ind := Induction for Wf Sort Prop.

Combined Scheme wt_mutual_ind from red_ind, wf_ind.
