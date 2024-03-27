Require Export typing.

Lemma here' : forall {A Γ T}, T = A ⟨shift⟩ ->  lookup 0 (A :: Γ) T.
Proof. move => > ->. by apply here. Qed.

Lemma there' : forall {n A Γ B T}, T = A ⟨shift⟩ ->
      lookup n Γ A -> lookup (S n) (B :: Γ) T.
Proof. move => > ->. by apply there. Qed.

Lemma WR_Conv Γ a b A B : Γ ⊢ a ▻ b ∈ A -> Γ ⊢ A ≡ B -> Γ ⊢ a ▻ b ∈ B.
Proof.
  move => + h. elim : A B / h; eauto with wt.
Qed.

Lemma WRs_Conv Γ a b A B : Γ ⊢ a ▻+ b ∈ A -> Γ ⊢ A ≡ B -> Γ ⊢ a ▻+ b ∈ B.
Proof.
  move => h. move : B.
  elim : Γ a b A / h; qauto l:on use:WR_Conv db:wt.
Qed.

Lemma WR_Conv' Γ a b A B : Γ ⊢ a ▻ b ∈ A -> Γ ⊢ B ≡ A -> Γ ⊢ a ▻ b ∈ B.
Proof. move => > + /Equiv_sym; apply WR_Conv. Qed.

Lemma good_renaming_up ξ Γ Δ A :
  lookup_good_renaming ξ Γ Δ ->
  lookup_good_renaming (upRen_tm_tm ξ)  (A :: Γ) (A⟨ξ⟩ :: Δ).
Proof.
  rewrite /lookup_good_renaming => h.
  move => i B.
  inversion 1 =>*; subst.
  - apply here'. by asimpl.
  - asimpl. apply : there'; eauto. by asimpl.
Qed.

Lemma WR_App' Γ A A' i B B' M M' N N' T :
  T = B[N..] ->
  Γ ⊢ A ▻ A' ∈ Univ i ->
  A :: Γ ⊢ B ▻ B' ∈ Univ i ->
  Γ ⊢ M ▻ M' ∈ Pi A B ->
  Γ ⊢ N ▻ N' ∈ A ->
  (* ------------------------ *)
  Γ ⊢ App A B M N ▻ App A' B' M' N' ∈ T.
Proof. move =>> ->. apply WR_App. Qed.

Lemma WR_Beta' Γ A i A' A0 B M M' N N' P T :
  P = M'[N'..] ->
  T = B[N..] ->
  Γ ⊢ A ▻ A ∈ Univ i ->
  Γ ⊢ A' ▻ A' ∈ Univ i ->
  Γ ⊢ A0 ▻+ A ∈ Univ i ->
  Γ ⊢ A0 ▻+ A' ∈ Univ i ->
  A :: Γ ⊢ B ▻ B ∈ Univ i ->
  A :: Γ ⊢ M ▻ M' ∈ B ->
  Γ ⊢ N ▻ N' ∈ A ->
  (*----------------------  *)
  Γ ⊢ App A' B (Lam A M) N ▻ P ∈ T.
Proof. move =>> -> ->. apply WR_Beta. Qed.

Lemma wt_renaming_mutual :
  (forall Γ a b A, Γ ⊢ a ▻ b ∈ A -> forall ξ Δ,
        lookup_good_renaming ξ Γ Δ -> Wf Δ -> Δ ⊢ a⟨ξ⟩ ▻ b⟨ξ⟩ ∈ A⟨ξ⟩ ) /\
  (forall Γ a b A, Γ ⊢ a ▻+ b ∈ A -> forall ξ Δ,
        lookup_good_renaming ξ Γ Δ -> Wf Δ -> Δ ⊢ a⟨ξ⟩ ▻+ b⟨ξ⟩ ∈ A⟨ξ⟩ ) /\
  (forall Γ, ⊢ Γ -> True).
Proof.
  apply wt_mutual_ind=>//; eauto with wt.
  - hauto lq:on unfold:lookup_good_renaming db:wt.
  - hauto q:on db:wt.
  - hauto q:on use:good_renaming_up db:wt.
  - hauto q:on use:good_renaming_up db:wt.
  - move => */=. apply : WR_App'; eauto using good_renaming_up with wt.
    by asimpl.
  - move => *. apply : WR_Beta';
      (* The two eautos is *NOT* a typo. Need to suppress the use of
      wt constructors to avoid prematurely instantiating ▻+ with the
      One constructor *)
      eauto using good_renaming_up;
      eauto using good_renaming_up with wt.
    by asimpl.
    by asimpl.
Qed.

Definition lookup_good_morphing ρ Γ Δ :=
  forall n A, lookup n Γ A -> Δ ⊢ ρ n ▻ ρ n ∈ A[ρ].

Lemma lookup_good_renaming_shift A Δ:
  lookup_good_renaming ↑ Δ (A :: Δ).
Proof. rewrite /lookup_good_renaming => >. apply there. Qed.

Lemma subst_ren_factor A ρ ξ :  A[ρ >> ren_tm ξ ] = A[ρ]⟨ξ⟩.
Proof. by asimpl. Qed.

Lemma good_morphing_up ρ k Γ Δ A B
  (h : lookup_good_morphing ρ Γ Δ) :
  Δ ⊢ A[ρ] ▻ B ∈ Univ k ->
  lookup_good_morphing (up_tm_tm ρ) (A :: Γ) (A [ρ] :: Δ).
Proof.
  rewrite /lookup_good_morphing => h1.
  inversion 1=>*; subst.
  - apply WR_Var => /=.
    + eauto with wt.
    + asimpl. apply : here'. by asimpl.
  - asimpl. rewrite !subst_ren_factor.
    eapply wt_renaming_mutual. hauto l:on unfold:lookup_good_morphing.
    apply lookup_good_renaming_shift.
    eauto with wt.
Qed.

Lemma wt_morphing_mutual :
  (forall Γ a b A, Γ ⊢ a ▻ b ∈ A -> forall ρ Δ,
        lookup_good_morphing ρ Γ Δ -> Wf Δ -> Δ ⊢ a[ρ] ▻ b[ρ] ∈ A[ρ] ) /\
  (forall Γ a b A, Γ ⊢ a ▻+ b ∈ A -> forall ρ Δ,
        lookup_good_morphing ρ Γ Δ -> Wf Δ -> Δ ⊢ a[ρ] ▻+ b[ρ] ∈ A[ρ] ) /\
  (forall Γ, ⊢ Γ -> True).
Proof.
  apply wt_mutual_ind=>//; eauto with wt.
  - hauto q:on db:wt.
  - hauto q:on use:good_morphing_up db:wt.
  - hauto q:on use:good_morphing_up db:wt.
  - move => *.
    apply : WR_App'; eauto. by asimpl. qauto l:on use:good_morphing_up db:wt.
  - move => Γ A i A' A0 B M M' N N' hA ihA hA' ihA' hA00 ihA00 hA01 ihA01 hB ihB hM ihM hN ihN ρ Δ hρ hΔ /=.
    apply : WR_Beta'; eauto; cycle 1.
    by asimpl.
    hauto lq:on use:good_morphing_up db:wt.
    hauto lq:on use:good_morphing_up db:wt.
    by asimpl.
Qed.

Lemma equiv_renaming Γ A B (h : Γ ⊢ A ≡ B) :
  forall ξ Δ, lookup_good_renaming ξ Γ Δ -> ⊢ Δ -> Δ ⊢ A⟨ξ⟩ ≡ B⟨ξ⟩.
Proof.
  elim : A B / h; hauto q:on ctrs:WtEquiv use:wt_renaming_mutual.
Qed.

Lemma wr_morphing :
  forall Γ a b A, Γ ⊢ a ▻ b ∈ A -> forall ρ Δ,
        lookup_good_morphing ρ Γ Δ -> Wf Δ -> Δ ⊢ a[ρ] ▻ b[ρ] ∈ A[ρ].
Proof. apply wt_morphing_mutual. Qed.

Lemma wrs_Equiv Γ A B i (h : Γ ⊢ A ▻+ B ∈ Univ i) : Γ ⊢ A ≡ B.
Proof.
  move E : (Univ i) h => T h.
  move : E.
  elim : A B T / h;
    hauto lq:on ctrs:WtEquiv.
Qed.

Lemma Conv_Equiv Γ A B C i :
  Γ ⊢ A ▻+ B ∈ Univ i ->
  Γ ⊢ A ▻+ C ∈ Univ i ->
  Γ ⊢ B ≡ C.
Proof.
  move => /wrs_Equiv /Equiv_sym + /wrs_Equiv.
  apply WE_Trans.
Qed.

Lemma Wt_Wf_mutual :
  (forall Γ a b A, Γ ⊢ a ▻ b ∈ A -> ⊢ Γ ) /\
  (forall Γ a b A, Γ ⊢ a ▻+ b ∈ A -> ⊢ Γ) /\
  (forall Γ, ⊢ Γ -> True).
Proof. apply wt_mutual_ind; eauto with wt. Qed.

Lemma Wf_cons_inv A Γ :
  ⊢ A :: Γ ->
  ⊢ Γ /\ exists B i, Γ ⊢ A ▻ B ∈ Univ i.
Proof. hauto l:on inv:Wf use:Wt_Wf_mutual. Qed.

Lemma lookup_good_id A A' Γ
  (h0 : ⊢ A' :: Γ)
  (h : Γ ⊢ A' ≡ A) :
  lookup_good_morphing var_tm (A :: Γ) (A' :: Γ).
Proof.
  move => k T.
  elim /lookup_inv => _.
  + move => ? ? ? []*. subst. asimpl.
    apply WR_Conv with (A := A' ⟨↑⟩).
    hauto q:on ctrs:WtRed, lookup.
    apply : equiv_renaming=>//; last by apply lookup_good_renaming_shift. exact h.
  + move => n A1 Γ0 B0 ? ? []*. subst.
    asimpl.
    change (var_tm (↑ n)) with ((var_tm n)⟨↑⟩).
    eapply wt_renaming_mutual=>//; last by apply lookup_good_renaming_shift.
    apply : WR_Var; eauto.
    sfirstorder use:Wf_cons_inv.
Qed.

Lemma Ctx_conv A B Γ M N C (h : A :: Γ ⊢ M ▻ N ∈ C) (h1 : Γ ⊢ A ≡ B)
  (h2 : ⊢ B :: Γ) :
  B :: Γ ⊢ M ▻ N ∈ C.
Proof.
  move /wr_morphing /(_ var_tm) : h. asimpl. apply=>//.
  apply lookup_good_id; eauto.
  move : h1. apply Equiv_sym.
Qed.

Lemma WRs_Ctx_conv A B Γ M N C (h : A :: Γ ⊢ M ▻+ N ∈ C) (h1 : Γ ⊢ A ≡ B)
  (h2 : ⊢ B :: Γ) :
  B :: Γ ⊢ M ▻+ N ∈ C.
Proof.
  move /(proj1 (proj2 wt_morphing_mutual)) /(_ var_tm) : h. asimpl. apply=>//.
  apply lookup_good_id; eauto.
  move : h1. apply Equiv_sym.
Qed.

Lemma lh_refl_helper Γ A0 A i B :
  Γ ⊢ A0 ▻+ A ∈ Univ i ->
  A :: Γ ⊢ B ▻ B ∈ Univ i ->
  Γ ⊢ Pi A0 B ▻+ Pi A B ∈ Univ i.
Proof.
  move E : (Univ i) => T h.
  move : i E.
  elim : Γ A0 A T / h.
  - move => Γ A0 A ? h i ? hB; subst.
    have ? : ⊢ A0 :: Γ by eauto with wt.
    apply WRs_One.
    apply : WR_Prod=>//.
    apply : Ctx_conv; eauto with wt.
  - move => Γ A A0 A1 T h0 h1 ih i ? h2. subst.
    specialize ih with (1 := eq_refl).
    move /ih : (h2) {ih}.
    apply : WRs_Trans.
    apply WR_Prod; eauto.
    apply : Ctx_conv; eauto with wt.
    hauto lq:on rew:off use:wrs_Equiv, Equiv_sym db:wt.
Qed.

Lemma lh_refl_mutual :
  (forall Γ a b A, Γ ⊢ a ▻ b ∈ A -> Γ ⊢ a ▻ a ∈ A ) /\
  (forall Γ a b A, Γ ⊢ a ▻+ b ∈ A -> Γ ⊢ a ▻ a ∈ A ) /\
  (forall Γ, ⊢ Γ -> True).
Proof.
  apply wt_mutual_ind=>//; eauto with wt.
  move => Γ A i A' A0 B M M' N N' h0 _  h1 _ hA00 ihA00 hA01 ihA01 hB ihB hM ihM hN ihN.
  have hequiv : Γ ⊢ A' ≡ A by eauto using Conv_Equiv.
  have /Equiv_sym hequiv_s := hequiv.
  apply : WR_App; eauto 1 with wt.
  - move => [:tr0].
    move : ihB. move/wr_morphing /(_ var_tm). asimpl. apply; last by abstract : tr0; eauto with wt.
    apply lookup_good_id; eauto.
  - apply : WR_Conv.
    + apply : WR_Lam; eauto.
    + have : Γ ⊢ Pi A0 B ▻+ Pi A B ∈ Univ i by eauto using lh_refl_helper.
      move /Ctx_conv /(_ ltac:(sfirstorder) ltac:(hauto lq:on db:wt)) in hB.
      have : Γ ⊢ Pi A0 B ▻+ Pi A' B ∈ Univ i by eauto using lh_refl_helper.
      move => /wrs_Equiv + /wrs_Equiv /Equiv_sym.
      move /[swap]. apply WE_Trans.
  - apply : WR_Conv; eauto.
Qed.

Definition lookup_good_morphing2 ρ0 ρ1 Γ Δ :=
  forall n A, lookup n Γ A -> Δ ⊢ ρ0 n ▻ ρ1 n ∈ A[ρ0].

Lemma good_morphing2_up ρ0 ρ1 A B k Γ Δ
  (h : lookup_good_morphing2 ρ0 ρ1 Γ Δ) :
  Δ ⊢ A[ρ0] ▻ B ∈ Univ k ->
  lookup_good_morphing2 (up_tm_tm ρ0) (up_tm_tm ρ1) (A :: Γ) (A[ρ0] :: Δ).
Proof.
  rewrite /lookup_good_morphing => h1.
  inversion 1=>*; subst.
  - apply WR_Var => /=.
    + eauto with wt.
    + asimpl. apply : here'. by asimpl.
  - asimpl. rewrite !subst_ren_factor.
    eapply wt_renaming_mutual. hauto l:on unfold:lookup_good_morphing.
    apply lookup_good_renaming_shift.
    eauto with wt.
Qed.

Lemma lookup_good_morphing2_lh_refl ρ0 ρ1 Γ Δ :
  lookup_good_morphing2 ρ0 ρ1 Γ Δ ->
  lookup_good_morphing2 ρ0 ρ0 Γ Δ.
Proof.
  hauto lq:on use:lh_refl_mutual unfold:lookup_good_morphing2.
Qed.

Lemma wt_morphing2_mutual :
  (forall Γ a b A, Γ ⊢ a ▻ b ∈ A -> forall ρ0 ρ1 Δ,
        lookup_good_morphing2 ρ0 ρ1 Γ Δ -> Wf Δ -> Δ ⊢ a[ρ0] ▻ b[ρ1] ∈ A[ρ0] ) /\
  (forall Γ a b A, Γ ⊢ a ▻+ b ∈ A -> forall ρ0 ρ1 Δ,
        lookup_good_morphing2 ρ0 ρ1 Γ Δ -> Wf Δ -> Δ ⊢ a[ρ0] ▻+ b[ρ1] ∈ A[ρ0] ) /\
  (forall Γ, ⊢ Γ -> True).
Proof.
  apply wt_mutual_ind; eauto with wt.
  - hauto q:on db:wt.
  - hauto q:on use:good_morphing2_up db:wt.
  - hauto q:on use:lookup_good_morphing2_lh_refl, good_morphing2_up db:wt.
  - move => *.
    apply : WR_App'; eauto. by asimpl. qauto l:on use:good_morphing2_up db:wt.
  - move => Γ A i A' A0 B M M' N N' hA ihA hA' ihA' hA00 ihA00 hA01 ihA01 hB ihB hM ihM hN ihN ρ0 ρ1 Δ hρ hΔ /=.
    apply WR_Beta' with (M' := M'[up_tm_tm ρ1]) (N' := N'[ρ1]) (A0 := A0[ρ0]) (i := i); eauto 3.
    + by asimpl.
    + by asimpl.
    + qauto l:on db:wt use:lh_refl_mutual.
    + hauto lq:on rew:off db:wt use:lh_refl_mutual.
    + sfirstorder use:lookup_good_morphing2_lh_refl.
    + sfirstorder use:lookup_good_morphing2_lh_refl.
    + hauto lq:on use:good_morphing2_up, lookup_good_morphing2_lh_refl db:wt.
    + hauto lq:on use:good_morphing2_up, lookup_good_morphing2_lh_refl db:wt.
  - qauto l:on use:lookup_good_morphing2_lh_refl, WR_Conv db:wt.
  - qauto l:on use:lookup_good_morphing2_lh_refl, WR_Conv db:wt.
  - eauto using lookup_good_morphing2_lh_refl with wt.
Qed.

Lemma WR_cong Γ A B B' T M M' :
  A :: Γ ⊢ B ▻ B' ∈ T ->
  Γ ⊢ M ▻ M' ∈ A ->
  Γ ⊢ B[M..] ▻ B'[M'..] ∈ T[M..].
Proof.
  move => + h.
  move /(proj1 wt_morphing2_mutual).
  apply; last by sfirstorder use:Wt_Wf_mutual.
  move => k A0.
  elim /lookup_inv=>_.
  - move => ? ? ? []*. subst. by asimpl.
  - move => n A1 Γ0 B0 ? ? []*. subst.
    asimpl. hauto lq:on use:Wt_Wf_mutual db:wt.
Qed.

(* This lemma is silly but I really need it because otherwise
automation gets blocked too easily *)
Lemma WR_cong_univ Γ A B B' i M M' :
  A :: Γ ⊢ B ▻ B' ∈ Univ i ->
  Γ ⊢ M ▻ M' ∈ A ->
  Γ ⊢ B[M..] ▻ B'[M'..] ∈ Univ i.
Proof. apply WR_cong. Qed.

Lemma rh_refl_mutual :
  (forall Γ a b A, Γ ⊢ a ▻ b ∈ A -> Γ ⊢ b ▻ b ∈ A ) /\
  (forall Γ a b A, Γ ⊢ a ▻+ b ∈ A -> Γ ⊢ b ▻ b ∈ A ) /\
  (forall Γ, ⊢ Γ -> True).
Proof.
  apply wt_mutual_ind; eauto with wt.
  - eauto using Ctx_conv with wt.
  - move => *.
    apply : WR_Conv; eauto with wt.
    hauto lq:on use:Ctx_conv db:wt.
  - move => Γ A A' i B B' M M' N N' hA ihA hB ihB hM ihM hN ihN.
    apply : WR_Conv; eauto with wt.
    apply : WR_App; eauto with wt.
    eauto using Ctx_conv with wt.
    apply : WE_Exp.
    apply /WR_cong : hB hN.
  - move => Γ A i A' A0 B M M' N N' hA ihA hA' ihA' hA00 ihA00 hA01 ihA01 hB _ hM ihM hN ihN.
    apply : WR_Conv.
    apply : WR_cong; eauto.
    apply : WE_Exp.
    apply /WR_cong : hB hN.
Qed.

Lemma lookup_wf Γ n A (h : ⊢ Γ) (h0 : lookup n Γ A) : exists i, Γ ⊢ A ▻ A ∈ Univ i.
Proof.
  move : h.
  elim : n Γ A / h0.
  - move => A Γ /Wf_cons_inv.
    move => [h0][B][i]h1.
    exists i.
    move /(proj1 lh_refl_mutual) : (h1).
    move/(proj1 wt_renaming_mutual).
    apply. by apply lookup_good_renaming_shift.
    by apply /Wf_cons : h1.
  - move => n A Γ B h ih /Wf_cons_inv.
    move => [/ih+][B0][i]h1.
    move => [j]h2.
    exists j.
    move/(proj1 wt_renaming_mutual) : h2.
    apply. by apply lookup_good_renaming_shift.
    apply /Wf_cons : h1.
Qed.

(* Adding Unit eta naively breaks inversion. Expand only when term is neutral? *)
(* Can the weakened inversion principle still allow us to derive the diamond property? *)
(* We can include the unit case still, but what properties can we recover? Diamond? Confluence? *)
(* Conjecture: The only thing that's compromised is the strength of
   progress + preservation. I think we can still prove it, but it
   doesn't tell us much about safety (e.g. how do we know that two
   booleans won't step into unit and becomes equal?) *)
(* For the diamond property to be provable, it is important that it
does not imply consistency *)
(* Actually, diamond doesn't even imply the consistency of the
equational theory. It's impossible to rule out Pi Bool Nat = () = Pi Nat Bool *)
(* What about removing exp? Expansion postponement? *)
(* Can we give a direct proof of diamond without the exp rule? *)
(* Can we prove exp a posteriori? *)
(* Would the system without exp be helpful as an intermediate system
for logical relations? *)
Lemma Univ_inv Γ i N T (h : Γ ⊢ Univ i ▻ N ∈ T) :
  N = Univ i /\ Γ ⊢ T ≡ Univ (S i).
Proof.
  move E : (Univ i) h => M h.
  move : i E.
  elim : Γ M N T / h=>//;hauto lq:on rew:off db:wt.
Qed.

Lemma Var_inv Γ n N T (h : Γ ⊢ var_tm n ▻ N ∈ T) :
  N = var_tm n /\ exists A, lookup n Γ A /\ Γ ⊢ T ≡ A.
Proof.
  move E : (var_tm n) h => M h.
  move : n E.
  elim : Γ M N T / h=>//.
  - hauto lq:on use:lookup_wf db:wt.
  - hauto lq:on rew:off db:wt.
  - hauto lq:on rew:off db:wt.
Qed.

Lemma Prod_inv Γ A B N T (h : Γ ⊢ Pi A B ▻ N ∈ T) :
  exists A' B' i, N = Pi A' B' /\ Γ ⊢ A ▻ A' ∈ Univ i /\ A::Γ ⊢ B ▻ B' ∈ Univ i /\ Γ ⊢ T ≡ Univ i.
Proof.
  move E : (Pi A B) h => M h.
  move : A B E.
  elim : Γ M N T / h=>//.
  - hauto lq:on use:Wt_Wf_mutual db:wt.
  - hauto lq:on rew:off db:wt.
  - hauto lq:on rew:off db:wt.
Qed.

Lemma Lam_inv Γ A M N T (h : Γ ⊢ Lam A M ▻ N ∈ T) :
  exists A' M' B i,
    N = Lam A' M' /\
    Γ ⊢ A ▻ A' ∈ Univ i /\
    A::Γ ⊢ B ▻ B ∈ Univ i /\
    A::Γ ⊢ M ▻ M' ∈ B /\
    Γ ⊢ T ≡ Pi A B.
Proof.
  move E : (Lam A M) h => M0 h.
  move : A M E.
  elim : Γ M0 N T / h=>//.
  - hauto lq:on use:Wt_Wf_mutual db:wt.
  - hauto lq:on rew:off db:wt.
  - hauto lq:on rew:off db:wt.
Qed.

Lemma App_inv Γ P U B Q N T (h : Γ ⊢ App U B P Q ▻ N ∈ T) :
  exists A A' B' Q' i,
    Γ ⊢ A ▻ A' ∈ Univ i /\ A::Γ ⊢ B ▻B' ∈ Univ i /\ Γ ⊢ Q ▻ Q' ∈ A /\
    Γ ⊢ T ≡ B[Q..] /\
    (* App case *)
    ((exists P', U = A /\ Γ ⊢ P ▻ P' ∈ Pi A B /\ N = App A' B' P' Q') \/
    (* Beta case *)
     (exists A0 A'' R R', U = A''/\ P = Lam A R /\ A::Γ ⊢ R ▻ R' ∈ B /\ N = R'[Q'..] /\
                         Γ ⊢ A0 ▻+ A'' ∈ Univ i /\ Γ ⊢ A0 ▻+ A ∈ Univ i)).
Proof.
  move E : (App U B P Q) h => M h.
  move : U B P Q E.
  elim : Γ M N T / h=>//.
  - move => Γ A A' i B B' M M' N N' hA _ hB _ hM _ hN _ >[]*. subst.
    exists A, A', B', N', i.
    repeat split => //.
    (* Factor out the first bullet *)
    + apply : WE_Red.
      move /WR_cong: hB hN. repeat move/[apply].
      apply /(proj1 lh_refl_mutual).
    + sfirstorder.
  - move => Γ A i A' A0 B M M' N N' hA _ hA' _ hA00 hA01 hB _ hM _ hN _ > []*.
    subst. exists A, A, B, N', i.
    repeat split => //.
    (* Factor out the first bullet *)
    + apply : WE_Red.
      move /WR_cong: hB hN. repeat move/[apply].
      apply /(proj1 lh_refl_mutual).
    + hauto lq:on.
  - hauto lq:on rew:off db:wt.
  - hauto lq:on rew:off db:wt.
Qed.

Lemma exchange : forall Γ M N A P B,
    Γ ⊢ M ▻ N ∈ A -> Γ ⊢ M ▻ P ∈ B -> Γ ⊢ M ▻ N ∈ B.
Proof.
  move => Γ M N A + + h.
  elim : Γ M N A / h; eauto 2.
  - hauto lq:on rew:off use:Var_inv.
  - hauto l:on use:Univ_inv.
  - move => Γ i A A' B B' hA ihA hB ihB P B0.
    move /Prod_inv.
    move => [A0][B1][i0][hA0][hB1][?]h.
    apply : WR_Conv'; eauto.
    hauto lq:on db:wt.
  - move => Γ A A' i B M M' h ihA hB ihB hM ihM P B0 /Lam_inv.
    move =>[A'0][M'0][B1][i0][?][?][?][?]?. subst.
    apply : WR_Conv'; eauto.
    move{i h hB}. eauto with wt.
  - move => Γ A A' i B B' M M' N N' hA ihA hB ihB hM ihM hN ihN P B0 /App_inv.
    move => [A0][A'0][B'0][Q'][i0][?][?][?][?]_.
    apply : WR_Conv'; eauto.
    hauto lq:on db:wt.
  - move => Γ A i A' A0 B M M' N N' hA ihA hA' ihA' hA0 ihA0 hA0' ihA0' hM ihM hN ihN P B0 /App_inv.
    (* Turns out the very cursed or condition isn't needed for either
    of the App cases *)
    move => [A1][A'0][B'][Q'][i0][?][?][?][?]_.
    apply : WR_Conv'; eauto.
    hauto lq:on db:wt.
Qed.

Lemma exchange_multi_step : forall Γ M N P A B,
  Γ ⊢ M ▻+ N ∈ A -> Γ ⊢ M ▻ P ∈ B -> Γ ⊢ M ▻+ N ∈ B.
Proof.
  move => Γ M N + A + h.
  elim : Γ M N A / h.
  - hauto lq:on use:exchange db:wt.
  - move => Γ M N P A h0 h1 ih P0 B h2.
    move => [:h3].
    apply : WRs_Trans.
    abstract : h3;  apply /exchange :h0 h2.
    move /(proj1 rh_refl_mutual) in h3.
    eauto.
Qed.

Lemma Prod_cong_stage0 Γ A0 A i B :
  Γ ⊢ A0 ▻+ A ∈ Univ i ->
  A0 :: Γ ⊢ B ▻ B ∈ Univ i ->
  Γ ⊢ Pi A0 B ▻+ Pi A B ∈ Univ i.
Proof.
  move => h h1.
  suff : A :: Γ ⊢ B ▻ B ∈ Univ i by sfirstorder use:lh_refl_helper.
  apply Ctx_conv with (A := A0); eauto with wt.
  apply /wrs_Equiv : h.
  hauto lq:on use:rh_refl_mutual db:wt.
Qed.

Lemma Prod_cong Γ A A' B B' i :
  Γ ⊢ A ▻+ A' ∈ Univ i ->
  A :: Γ ⊢ B ▻+ B' ∈ Univ i ->
  Γ ⊢ Pi A B ▻+ Pi A' B' ∈ Univ i.
Proof.
  move E : (A :: Γ) => Δ.
  move E0 : (Univ i) => T + h.
  move : A Γ i E E0.
  elim : Δ B B' T / h.
  - move => Γ M N A h A0 Γ0 i ? ? h1. subst.
    have : Γ0 ⊢ Pi A0 M ▻ Pi A0 N ∈ Univ i by
      hauto lq:on use:lh_refl_mutual db:wt.
    move / WRs_Trans. apply.
    apply Prod_cong_stage0; eauto. sfirstorder use:rh_refl_mutual.
  - move => Γ M N P A hM hN ih A0 Γ0 i ? ? h. subst.
    specialize ih with (1 := eq_refl) (2 := eq_refl) (3 := h).
    move /WRs_Trans : ih. apply.
    hauto lq:on use:lh_refl_mutual db:wt.
Qed.

Lemma Lam_cong Γ A A' M M' B C i :
  Γ ⊢ A ▻+ A' ∈ Univ i ->
  A :: Γ ⊢ M ▻+ M' ∈ B ->
  A :: Γ ⊢ B ▻ C ∈ Univ i ->
  Γ ⊢ Lam A M ▻+ Lam A' M' ∈ Pi A B.
Proof.
  move E : (A :: Γ) => Δ + h.
  move : A Γ E A' C i.
  elim : Δ M M' B / h.
  - move => Γ M N B h A0 Γ0 ? A' C i h0 h1. subst.
    have : Γ0 ⊢ Lam A0 M ▻ Lam A0 N ∈ Pi A0 B by
      hauto lq:on use:lh_refl_mutual db:wt.
    move /WRs_Trans. apply.
    move E : (Univ i) h0 =>T h0.
    move : i E h h1.
    elim : Γ0 A0 A' T / h0.
    + move => Γ A0 A1 ? h i ? h0 h1; subst.
      apply : WRs_One.
      apply : WR_Lam; eauto; sfirstorder use:lh_refl_mutual, rh_refl_mutual.
    + move => Γ A0 A1 A2 ? h0 h1 ih i ? h2 h3. subst.
      move => [:tr0].
      apply WRs_Trans with (N := Lam A1 N).
      abstract : tr0.
      qauto l:on use:lh_refl_mutual, rh_refl_mutual db:wt.
      specialize ih with (1 := eq_refl).
      move /Ctx_conv in h2.
      move /Ctx_conv in h3.
      have h4 : Γ ⊢ A0 ≡ A1 by qauto l:on db:wt.
      have h5 : ⊢ A1 :: Γ by qauto l:on inv:WtReds db:wt.
      move /(_ _ h4 h5) in h2.
      move /(_ _ h4 h5) in h3.
      move /(_ h2 h3) : ih.
      move /(proj1 rh_refl_mutual) /exchange_multi_step : tr0.
      apply.
  - move => Γ M N P A hM hN ih A0 Γ0 ? A' C i h0 h1; subst.
    specialize ih with (1 := eq_refl) (2 := h0) (3 := h1).
    apply : WRs_Trans; last by exact ih.
    qauto l:on use:lh_refl_mutual db:wt.
Qed.


Lemma wr_lh_refl :
  (forall Γ a b A, Γ ⊢ a ▻ b ∈ A -> Γ ⊢ a ▻ a ∈ A ).
Proof. exact (proj1 lh_refl_mutual). Qed.

Lemma wrs_lh_refl :
  (forall Γ a b A, Γ ⊢ a ▻+ b ∈ A -> Γ ⊢ a ▻ a ∈ A ).
Proof. exact (proj1 (proj2 lh_refl_mutual)). Qed.

Lemma wr_rh_refl :
  (forall Γ a b A, Γ ⊢ a ▻ b ∈ A -> Γ ⊢ b ▻ b ∈ A ).
Proof. exact (proj1 rh_refl_mutual). Qed.

Lemma wrs_rh_refl :
  (forall Γ a b A, Γ ⊢ a ▻+ b ∈ A -> Γ ⊢ b ▻ b ∈ A ).
Proof. exact (proj1 (proj2 rh_refl_mutual)). Qed.

#[export]Hint Resolve wr_lh_refl wrs_lh_refl wr_rh_refl wrs_rh_refl : wt.

Lemma Ctx_step A B i Γ M N C (h : A :: Γ ⊢ M ▻ N ∈ C) (h1 : Γ ⊢ A ▻ B ∈ Univ i) :
  B :: Γ ⊢ M ▻ N ∈ C.
Proof.
  apply : Ctx_conv; eauto with wt.
Qed.

Lemma WRs_Ctx_step A B i Γ M N C (h : A :: Γ ⊢ M ▻+ N ∈ C) (h1 : Γ ⊢ A ▻ B ∈ Univ i) :
  B :: Γ ⊢ M ▻+ N ∈ C.
Proof.
  apply : WRs_Ctx_conv; eauto with wt.
Qed.


#[export]Hint Resolve Ctx_step : wt.

Lemma App_cong Γ A A' i B B' M M' N N' :
  Γ ⊢ A ▻+ A' ∈ Univ i ->
  A :: Γ ⊢ B ▻+ B' ∈ Univ i ->
  Γ ⊢ M ▻+ M' ∈ Pi A B ->
  Γ ⊢ N ▻+ N' ∈ A ->
  Γ ⊢ App A B M N ▻+ App A' B' M' N' ∈ B[N..].
Proof.
  move E  : (Univ i) => T h.
  move : B B' M M' N N' i E.
  elim : Γ A A' T / h.
  - move => Γ M N A h B B' M0 M' N0 N' i ? h0 h1 h2. subst.
    apply WRs_Trans with (N := App N B M0 N0).
    apply WR_App with (i := i); eauto 3 with wt.
    have : Γ ⊢ M0 ▻+ M' ∈ Pi N B.
    apply : WRs_Conv; eauto.
    apply wrs_Equiv with (i := i).
    apply WRs_One.
    apply WR_Prod; eauto with wt.
    move /WRs_Ctx_step in h0. move/(_ _ _ ltac:(by eauto with wt)) in h0.
    move /WRs_Conv in h2.
    move /(_ N ltac:(by eauto with wt)) in h2.
    move /wr_rh_refl in h.
    move {h1}  => h1 {M}.
    move E : (N :: Γ)  h0 M0 M' N0 N' h1 h2 => Δ h0.
    move : E.
    move E : (Univ i) h0  => T h0.
    move : E.
    elim : Δ B B' T / h0.
    + move => ? P P' A h0 ? ? M0 M' Q Q' h2 h3. subst.
      apply (WRs_Trans _ _ (App N P' M0 Q)).
      apply : WR_App; eauto with wt.
      apply (WRs_Conv _ _ _ P'[Q..]); cycle 1.
      apply WE_Exp with (i := i).
      change (Univ i) with (Univ i)[Q..].
      eauto using WR_cong with wt.
      have : Γ ⊢ Pi N P ≡ Pi N P' by eauto with wt.
      move  /WRs_Conv : h2. move/[apply] => h2.
      move /wr_rh_refl in h0.
      move {P}.
      move : Q Q' h3.
      move E : (Pi N P') h2  => T h2.
      move : h h0 E.
      elim : Γ M0 M' T / h2.
      * move => Γ M M' A hM hN hP' ? Q Q' hQ. subst.
        apply WRs_Trans with (N := App N P' M' Q); first by eauto with wt.
        move /wr_rh_refl in hM. move{M}.
        move : hN hP' hM.
        elim : Γ Q Q' N  / hQ; first by eauto with wt.
        move => Γ M0 M1 M2 A hM0 hM1 ih hA hP' hM'.
        apply WRs_Trans with (N := App A P' M' M1); first by eauto with wt.
        move /(_ hA hP' hM') : ih.
        move /WRs_Conv. apply.
        apply WE_Exp with (i := i).
        eauto using WR_cong_univ with wt.
      * hauto lq:on db:wt.
    + move => Γ0 M0 N0 P A hM0 hN0 ih ? ? M1 M' N1 N' h0 h1. subst.
      specialize ih with (1 := eq_refl) (2 := eq_refl).
      apply WRs_Trans with (N := App N N0 M1 N1).
      apply WR_App with (i := i); eauto with wt.
      apply : WRs_Conv.
      apply ih; eauto with wt.
      eauto using WRs_Conv with wt.
      eauto using WR_cong_univ with wt.
  - move => Γ M N P A hM hN ih B B' M0 M' N0 N' i ? hB hM0 hN0. subst.
    have h0 : Γ ⊢ M ≡ N by eauto with wt.
    have h1 : ⊢ N :: Γ by qauto l:on use:rh_refl_mutual db:wt.
    specialize ih with (1 := eq_refl).
    apply WRs_Trans with (N := App N B M0 N0).
    apply WR_App with (i := i); sfirstorder use:lh_refl_mutual.
    apply ih.
    move : WRs_Ctx_conv hB (h0) (h1); repeat move/[apply]. exact.
    apply : WRs_Conv; eauto.
    apply : (wrs_Equiv _ _ _ i).
    apply WRs_One.
    apply WR_Prod=>//. sfirstorder use:lh_refl_mutual.
    apply : WRs_Conv; eauto.
Qed.

Lemma Prod_multi_inv Γ A B N T :
  Γ ⊢ Pi A B ▻+ N ∈ T ->
  exists A' B' i,
    N = Pi A' B' /\ Γ ⊢ A ▻+ A' ∈ Univ i /\ A :: Γ ⊢ B ▻+ B' ∈ Univ i  /\ Γ ⊢ T ≡ Univ i.
Proof.
  move E : (Pi A B) => U h.
  move : A B E. elim : Γ U N T / h.
  - move => > h *. subst.
    move /Prod_inv in h.
    hauto lq:on db:wt.
  - move => Γ M N PA A hM hN ih A0 B ?. subst.
    move /Prod_inv : hM.
    move =>[A'][B'][i][?][h0][h1]h2. subst.
    specialize ih with (1 := eq_refl).
    move : ih => [A'0][B'0][i0][?][h3][h4]h5. subst.
    exists A'0, B'0, i. repeat split =>//.
    apply : WRs_Trans; first by eassumption.
    move /wr_rh_refl : h0.
    move :h3. apply exchange_multi_step.
    move /Ctx_step /(_ h0) in h1.
    apply : WRs_Ctx_conv; eauto with wt.
    apply : WRs_Trans; first by eassumption.
    move /wr_rh_refl : h1.
    move : h4. apply exchange_multi_step.
Qed.

Lemma Lam_multi_inv Γ A M N T
  (h : Γ ⊢ Lam A M ▻+ N ∈ T) :
  exists A' M' B i,
    N = Lam A' M' /\
    Γ ⊢ A ▻+ A' ∈ Univ i /\
    A::Γ ⊢ B ▻ B ∈ Univ i /\
    A::Γ ⊢ M ▻+ M' ∈ B /\
    Γ ⊢ T ≡ Pi A B.
Proof.
  move E : (Lam A M) h => A0 h.
  move : A M E.
  elim : Γ A0 N T / h.
  - move => > h *. subst.
    move /Lam_inv in h.
    hauto lq:on db:wt.
  - move => Γ M N P A h0 h1 ih A0 M0 ?. subst.
    move /Lam_inv : h0 => [A'][M'][B][i][?][h2][h3][h4]h9. subst.
    specialize ih with (1 := eq_refl).
    move : ih=>[A'0][M'0][B'][i0][?][h5][h6][h7]h8. subst.
    exists A'0, M'0, B, i. repeat split =>//.
    apply : WRs_Trans; eauto 2.
    hauto lq:on rew:off use:exchange_multi_step db:wt.
    apply : WRs_Ctx_conv; eauto 2 with wt.
    move /Ctx_step /(_ h2) in h4.
    hauto lq:on rew:off use:exchange_multi_step db:wt.
Qed.

Lemma Univ_multi_inv Γ i N T (h : Γ ⊢ Univ i ▻+ N ∈ T) :
  N = Univ i /\ Γ ⊢ T ≡ Univ (S i).
Proof.
  move E : (Univ i) h => U h.
  move : E.
  elim : Γ U N T / h.
  - move => > h *. subst. move/Univ_inv in h. hauto lq:on db:wt.
  - move => Γ M N P A + h1 ih ?. subst.
    move /Univ_inv => [?]h2. subst.
    sfirstorder.
Qed.

Lemma regularity Γ M N A
  (h : Γ ⊢ M ▻ N ∈ A) :
  exists i, Γ ⊢ A ▻ A ∈ Univ i.
Proof.
  elim : Γ M N A / h; eauto with wt.
  - sfirstorder use:lookup_wf.
  - move => Γ A A' i B B' M M' N N' hA
             [i0 ihA] hB [i1 ihB] hM [i2 ihM] hN [i3 ihN].
    move /Prod_inv : ihM.
    move => [A'0][B'0][i4][?][?]?.
    exists i4. change (Univ i4) with (Univ i4)[N..].
    qauto l:on use:WR_cong, lh_refl_mutual, rh_refl_mutual db:wt.
  - move => Γ A i A' A0 B M M' N N' hA [i0 ihA] hA' [i1 ihA']
             hA0 hA0' hB [i2 ihB] hM [i3 ihM] hN [i4 ihN].
    exists i3.
    change (Univ i3) with (Univ i3)[N..].
    qauto l:on use:WR_cong, lh_refl_mutual, rh_refl_mutual db:wt.
Qed.

Lemma WRs_Trans0 Γ a b c A : Γ ⊢ a ▻+ b ∈ A -> Γ ⊢ b ▻+ c ∈ A -> Γ ⊢ a ▻+ c ∈ A.
Proof.
  move => h. move : c.
  elim : Γ a b A / h; eauto with wt.
Qed.

Lemma WRs_TransR Γ a b c A : Γ ⊢ a ▻+ b ∈ A -> Γ ⊢ b ▻ c ∈ A -> Γ ⊢ a ▻+ c ∈ A.
Proof.
  eauto using WRs_Trans0 with wt.
Qed.

Lemma wr_diamond : forall Γ M N A P B, Γ ⊢ M ▻ N ∈ A -> Γ ⊢ M ▻ P ∈ B -> exists Q, Γ ⊢ N ▻ Q ∈ B /\ Γ ⊢ P ▻ Q ∈ A.
Proof.
  move => Γ M N A + + h.
  elim : Γ M N A / h.
  - hauto lq:on rew:off ctrs:WtRed use:Var_inv.
  - qauto l:on ctrs:WtRed use:Univ_inv.
  - move => Γ i A A' B B' hA ihA hB ihB P B0 /Prod_inv.
    move => [A'0][B'0][i0][?][h0][h1]h2. subst.
    move /ihA : (h0) => [A''][hA0]hA1.
    move /ihB : (h1) => [B''][hB0]hB1.
    exists (Pi A'' B'').
    split; eauto with wt.
    apply WR_Conv' with (A := Univ i0)=>//.
    eauto with wt.
  - move => Γ A A' i B M M' hA ihA hB ihB hM ihM P B0 /Lam_inv.
    move => [A'0][M'0][B1][i0][?][h0][h1][h2]h3. subst.
    move /ihA : (h0) => [A''][hA0]hA1.
    move /ihM : (h2) => [M''][hM0]hM1.
    exists (Lam A'' M'').
    split; eauto with wt.
    + apply WR_Conv' with (A := Pi A' B1)=>//.
      by eauto with wt.
      by eauto using exchange with wt.
    + apply WR_Conv' with (A := Pi A'0 B).
      by eauto with wt.
      by eauto using exchange with wt.
  - move => Γ A A' i B B' M M' N N' hA ihA hB ihB hM ihM hN ihN P B0 /App_inv.
    move => [A0][A'0][B'0][Q'][i0][h0][h1][h2][h3][].
    + move => [M0][?][hM0]?. subst.
      move /ihM : (hM0) => [M''][h4]h5.
      move /ihN : (h2) => [N0][h6]h7.
      move /ihA : (h0) => [A''][h8]h9.
      move /ihB : (h1) => [B''][h10]h11.
      exists (App A'' B'' M'' N0). split.
      * apply WR_Conv' with (A := B'[N'..]).
        apply WR_App with (i := i0); eauto with wt.
        move /WE_Trans : h3. apply.
        eauto using WR_cong_univ with wt.
      * apply WR_Conv' with (A := B'0[Q'..]).
        apply WR_App with (i := i0); eauto using exchange with wt.
        eauto using WR_cong_univ with wt.
    + move => [A1][A''][M0][M0'][?][?][hM0][?][hA1]hA'. subst.
      rename A'' into A.
      have hL : Γ ⊢ Lam A0 M0 ▻ Lam A'0 M0' ∈ Pi A0 B by eauto with wt.
      move /ihM : (hL) => [M''][hM1]/Lam_inv.
      move => [A'1][M'0][B1][i1][?][hL0][hL1][hL2]hL3. subst.
      rename M'0 into M''.
      have heq : Γ ⊢ A0 ≡ A by eauto using wrs_Equiv, Equiv_sym with wt.
      have : A :: Γ ⊢ B ▻ B'0 ∈ Univ i0.
      apply Ctx_conv with (A := A0); eauto with wt.
      move /ihB => [B''][hB0]hB1.
      move /ihN : (h2) => [N''][hN0]hN1.
      move /Lam_inv : hM => [A'2][ M'0][ B2] [i2][?][hA0][hB2][hM2]he. subst.
      move /Lam_inv : hM1 => [A'3][M'][B3][i3][[? ?]][hA2][hB3][hM3]he'. subst.
      have heq' : Γ ⊢ A ≡ A'2 by
          move /Equiv_sym /WE_Trans : heq; apply;  eauto with wt.
      (* have hh : A::Γ ⊢ B' ≡ B  by eauto with wt. *)
      exists M'[N''..].
      split.
      * apply : WR_Conv'; eauto.
        apply WR_Exp with (i := i) (A := B'[N'..]); cycle 1.
        apply WR_cong_univ with (A := A); eauto.
        have h : Γ ⊢ A0 ▻ A'2 ∈ Univ i0 by eauto using exchange with wt.
        apply WR_Beta with (A0 := A1) (i := i0);
          eauto 4 using exchange, WRs_TransR, Ctx_conv with wt.
        move /exchange : hM3. apply.
        apply wr_rh_refl with (a := M0).
        apply : Ctx_step; eauto.
        move /exchange : hM2. apply.
        apply wr_lh_refl with (b := M0').
        apply : WR_Conv; eauto.
        apply : WE_Red.
        apply : Ctx_conv; eauto using Equiv_sym with wt.
      * rename Q' into N0.
        eapply WR_Exp with (A := B[N0..]);
          last by apply : WR_cong_univ; eauto with wt.
        apply WR_cong with (A := A); last by assumption.
        apply : exchange.
        move : hL2.
        move /Ctx_conv. apply; eauto with wt.
        apply : wr_rh_refl.
        apply : Ctx_conv.
        move : hM0; eauto.
        eauto. eauto with wt.
  - move => Γ A0 i A1 _A B0 M M' N N' hA0 ihA0 hA1 ihA1 _hA0 _hA1 hB0 ihB0 hM ihM hN ihN ? T.
    move /App_inv => [A2] [A'] [B1] [N0'][i0][hA2][hB1][hN'][hB2][].
    + move => [?][?][hA3]?. subst.
      move /Lam_inv : hA3 => [A0'][M0'][B'][i1][?][hA3][hB'][hM']heq. subst.
      move /ihM  : hM' {ihM} => [M''][hM0'']hM1''.
      move /ihN : (hN') {ihN} => [N''][hN0'']hN1''.
      exists M''[N''..].
      split.
      * apply : WR_Conv'; eauto.
        eapply WR_Exp with (A := B0[N'..]).
        apply : WR_cong; eauto using exchange with wt.
        apply : WR_cong_univ; eauto with wt.
      * eapply WR_Exp with (A := B1[N0'..]).
        have ?  : Γ ⊢ A0 ▻ A0' ∈ Univ i by eauto using exchange with wt.
        have ? : Γ ⊢ A2 ▻ A' ∈ Univ i by eauto using exchange with wt.
        have ? : Γ ⊢ _A ▻+ A0' ∈ Univ i by eauto using WRs_TransR.
        have ? : Γ ⊢ _A ▻+ A' ∈ Univ i by eauto using WRs_TransR.
        have ? : Γ ⊢ A2 ≡ A0' by eauto using Conv_Equiv.
        have ? : Γ ⊢ A0 ≡ A2 by eauto using Conv_Equiv.
        have ? : Γ ⊢ A2 ≡ A0 by eauto using Equiv_sym.
        apply WR_Beta with (A0 := _A) (i := i); eauto 3 using exchange, WRs_TransR with wt.
        have ? : A2 :: Γ ⊢ B0 ▻ B0 ∈ Univ i by
          apply Ctx_conv with (A := A0); eauto 3 using exchange with wt.
        apply Ctx_conv with (A := A2); eauto 3 using exchange with wt.
        eapply Ctx_step with (A := A0); eauto.
        apply : WR_Red; eauto.
        apply Ctx_conv with (A := A2); eauto 3 with wt.
        apply : WR_cong_univ; eauto.
    + move => [_A0][?][?][M0'][<-][[<- <-]][hM'][?][_hA2]_hA3. subst.
      move /ihM  : hM' {ihM} => [M''][hM0'']hM1''.
      move /ihN : (hN') {ihN} => [N''][hN0'']hN1''.
      exists M''[N''..]. split.
      * apply : WR_Conv'; eauto.
        apply : WR_Exp.
        apply : WR_cong; eauto using exchange with wt.
        apply : WR_cong_univ; eauto.
      * apply : WR_Exp.
        apply : WR_cong; eauto using exchange with wt.
        apply : WR_cong_univ; eauto using exchange.
  - hauto lq:on db:wt.
  - hauto lq:on db:wt.
Qed.
