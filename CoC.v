(******************************************************************************)
(*      Copyright (c) 2019 - Paulo Torrens <paulotorrens AT gnu DOT org>      *)
(******************************************************************************)
(** * The Calculus of Constructions *)

Require Import Arith.
Require Import Compare_dec.
Require Import Relations.
Require Import Equality.

(** ** Syntax

    The syntax for our lambda calculus. The [type] and [prop] are our universes,
    and we use de Bruijn indexes on the [bound] constructor. The standard [pi],
    [lambda] and [application] constructors are self-explanatory. Some auxiliary
    notation is also defined. *)

Inductive pseudoterm: Set :=
  | type
  | prop
  | bound (n: nat)
  | pi (t: pseudoterm) (b: pseudoterm)
  | lambda (t: pseudoterm) (b: pseudoterm)
  | application (f: pseudoterm) (x: pseudoterm).

Hint Constructors pseudoterm: coc.

Bind Scope coc_scope with pseudoterm.
Coercion bound: nat >-> pseudoterm.
Notation "\/ t , b" := (pi t b)
  (at level 70, t at level 70, b at level 70, format "\/ t ,  b"): coc_scope.
Notation "\ t , b" := (lambda t b)
  (at level 70, t at level 70, b at level 70, format "\ t ,  b"): coc_scope.
Notation "f @ x" := (application f x)
  (at level 65, x at level 65, left associativity): coc_scope.

(** A subterm relation [subterm a b] defines that [a] is a direct subterm of
   [b]. This is useful for checking that our one-step reduction may be applied
   at any depth. *)

Inductive subterm: pseudoterm -> pseudoterm -> Prop :=
  | subterm_pi_left:
    forall t b, subterm t (\/t, b)
  | subterm_pi_right:
    forall t b, subterm b (\/t, b)
  | subterm_lambda_left:
    forall t b, subterm t (\t, b)
  | subterm_lambda_right:
    forall t b, subterm b (\t, b)
  | subterm_application_left:
    forall f x, subterm f (f @ x)
  | subterm_application_right:
    forall f x, subterm x (f @ x).

Hint Constructors subterm: coc.

(** ** Lifting

    Since we're dealing with de Bruijn index, we need a notion of lifting for
    bound variables, used whenever we add an existing pseudoterm inside of a new
    abstraction. Lifting is also used by the notion of substitution. *)

Fixpoint lift (i: nat) (k: nat) (e: pseudoterm): pseudoterm :=
  match e with
  | type =>
    type
  | prop =>
    prop
  | bound n =>
    if le_gt_dec k n then
      bound (i + n)
    else
      bound n
  | pi t b =>
    pi (lift i k t) (lift i (S k) b)
  | lambda t b =>
    lambda (lift i k t) (lift i (S k) b)
  | application f x =>
    application (lift i k f) (lift i k x)
  end.

Lemma lift_distributes_over_pi:
  forall t b i k,
  lift i k (pi t b) = pi (lift i k t) (lift i (S k) b).
Proof.
  auto.
Qed.

Hint Resolve lift_distributes_over_pi: coc.

Lemma lift_distributes_over_lambda:
  forall t b i k,
  lift i k (lambda t b) = lambda (lift i k t) (lift i (S k) b).
Proof.
  auto.
Qed.

Hint Resolve lift_distributes_over_lambda: coc.

Lemma lift_distributes_over_application:
  forall f x i k,
  lift i k (application f x) = application (lift i k f) (lift i k x).
Proof.
  auto.
Qed.

Hint Resolve lift_distributes_over_application: coc.

Lemma lift_zero_e_equals_e:
  forall e k,
  lift 0 k e = e.
Proof.
  induction e; intros.
  (* Case: type. *)
  - auto.
  (* Case: prop. *)
  - auto.
  (* Case: bound. *)
  - simpl.
    destruct (le_gt_dec k n); reflexivity.
  (* Case: pi. *)
  - simpl.
    rewrite (IHe1 k).
    rewrite (IHe2 (S k)).
    reflexivity.
  (* Case: lambda. *)
  - simpl.
    rewrite (IHe1 k).
    rewrite (IHe2 (S k)).
    reflexivity.
  (* Case: application. *)
  - simpl.
    rewrite (IHe1 k).
    rewrite (IHe2 k).
    reflexivity.
Qed.

Lemma lift_bound_ge:
  forall i k n,
  k <= n -> lift i k n = i + n.
Proof.
  intros; simpl.
  destruct (le_gt_dec k n).
  (* Case: k <= n. *)
  - reflexivity.
  (* Case: k > n. *)
  - absurd (k <= n); auto with arith.
Qed.

Lemma lift_bound_lt:
  forall i k n,
  k > n -> lift i k n = n.
Proof.
  intros; simpl.
  destruct (le_gt_dec k n).
  - absurd (k <= n); auto with arith.
  - reflexivity.
Qed.

Lemma lift_i_lift_j_equals_lift_i_plus_j:
  forall e i j k,
  lift i k (lift j k e) = lift (i + j) k e.
Proof.
  induction e; intros.
  (* Case: type. *)
  - auto.
  (* Case: prop. *)
  - auto.
  (* Case: bound. *)
  - simpl.
    destruct (le_gt_dec k n).
    + rewrite plus_assoc_reverse.
      apply lift_bound_ge.
      apply le_trans with n; auto.
      apply le_plus_r.
    + apply lift_bound_lt; auto.
  (* Case: pi. *)
  - intros; simpl; f_equal; auto.
  (* Case: lambda. *)
  - intros; simpl; f_equal; auto.
  (* Case: application. *)
  - intros; simpl; f_equal; auto.
Qed.

Lemma lift_lift_simplification:
  forall e i j k l,
  k <= l + j -> l <= k -> lift i k (lift j l e) = lift (i + j) l e.
Proof.
  induction e; intros.
  (* Case: type. *)
  - auto.
  (* Case: prop. *)
  - auto.
  (* Case: bound. *)
  - simpl.
    destruct (le_gt_dec l n).
    + rewrite lift_bound_ge; auto with arith.
      apply le_trans with (l + j); auto.
      replace (l + j) with (j + l); auto with arith.
    + rewrite lift_bound_lt; eauto with arith.
  (* Case: pi. *)
  - simpl; f_equal.
    rewrite IHe1; auto.
    rewrite IHe2; auto with arith.
    eauto with arith.
  (* Case: lambda. *)
  - simpl; f_equal.
    rewrite IHe1; auto.
    rewrite IHe2; auto with arith.
    eauto with arith.
  (* Case: application. *)
  - simpl; f_equal.
    rewrite IHe1; auto.
    rewrite IHe2; auto with arith.
Qed.

Lemma lift_lift_permutation:
  forall e i j k l,
  k <= l -> lift i k (lift j l e) = lift j (i + l) (lift i k e).
Proof.
  induction e; intros.
  (* Case: type. *)
  - auto.
  (* Case: prop. *)
  - auto.
  (* Case: bound. *)
  - simpl.
    destruct (le_gt_dec l n); destruct (le_gt_dec k n); intros.
    + rewrite lift_bound_ge.
      rewrite lift_bound_ge; auto with arith.
      do 2 elim plus_assoc_reverse; auto with arith.
      eapply le_trans; eauto with arith.
    + absurd (k <= n); eauto with arith.
    + rewrite lift_bound_ge; auto.
      rewrite lift_bound_lt; auto.
      auto with arith.
    + rewrite lift_bound_lt; auto.
      rewrite lift_bound_lt; auto.
      eauto with arith.
  (* Case: pi. *)
  - simpl; f_equal.
    apply IHe1; auto.
    replace (S (i + l)) with (i + S l); auto.
    apply IHe2; auto with arith.
  (* Case: lambda. *)
  - simpl; f_equal.
    apply IHe1; auto.
    replace (S (i + l)) with (i + S l); auto.
    apply IHe2; auto with arith.
  (* Case: application. *)
  - simpl; f_equal.
    apply IHe1; auto.
    apply IHe2; auto.
Qed.

(** ** Substitution *)

Fixpoint subst (p: pseudoterm) (k: nat) (q: pseudoterm): pseudoterm :=
  match q with
  | type =>
    type
  | prop =>
    prop
  | bound n =>
    match lt_eq_lt_dec k n with
    | inleft (left _) => bound (pred n)
    | inleft (right _) => lift k 0 p
    | inright _ => bound n
    end
  | pi t b =>
    pi (subst p k t) (subst p (S k) b)
  | lambda t b =>
    lambda (subst p k t) (subst p (S k) b)
  | application f x =>
    application (subst p k f) (subst p k x)
  end.

Notation "q [ p /]" := (subst p 0 q)
  (at level 1, format "q [ p /]"): coc_scope.

Lemma subst_distributes_over_pi:
  forall t b i k,
  subst i k (pi t b) = pi (subst i k t) (subst i (S k) b).
Proof.
  auto.
Qed.

Hint Resolve subst_distributes_over_pi: coc.

Lemma subst_distributes_over_lambda:
  forall t b i k,
  subst i k (lambda t b) = lambda (subst i k t) (subst i (S k) b).
Proof.
  auto.
Qed.

Hint Resolve subst_distributes_over_lambda: coc.

Lemma subst_distributes_over_application:
  forall f x i k,
  subst i k (application f x) = application (subst i k f) (subst i k x).
Proof.
  auto.
Qed.

Hint Resolve subst_distributes_over_application: coc.

Lemma subst_bound_gt:
  forall e k n,
  n > k -> subst e k n = pred n.
Proof.
  intros; simpl.
  destruct (lt_eq_lt_dec k n) as [ [ ? | ? ] | ? ].
  - reflexivity.
  - elim gt_irrefl with k; congruence.
  - absurd (k <= n); auto with arith.
Qed.

Lemma subst_bound_eq:
  forall e k n,
  n = k -> subst e k n = lift n 0 e.
Proof.
  destruct 1; simpl.
  destruct (lt_eq_lt_dec n n) as [ [ ? | ? ] | ? ].
  - destruct (gt_irrefl n); auto.
  - reflexivity.
  - destruct (lt_irrefl n); auto.
Qed.

Lemma subst_bound_lt:
  forall e k n,
  n < k -> subst e k n = n.
Proof.
  intros; simpl.
  destruct (lt_eq_lt_dec k n) as [ [ ? | ? ] | ? ].
  - absurd (k <= n); auto with arith.
  - elim lt_irrefl with k; congruence.
  - reflexivity.
Qed.

Lemma lift_addition_distributes_over_subst:
  forall a b i p k,
  lift i (p + k) (subst b p a) = subst (lift i k b) p (lift i (S (p + k)) a).
Proof.
  induction a; intros.
  (* Case: type. *)
  - reflexivity.
  (* Case: prop. *)
  - reflexivity.
  (* Case: bound. *)
  - unfold subst at 1.
    destruct (lt_eq_lt_dec p n) as [ [ ? | ? ] | ? ].
    + destruct n.
      inversion l.
      unfold lift at 1, pred.
      destruct (le_gt_dec (p + k) n).
      * rewrite lift_bound_ge; auto with arith.
        rewrite subst_bound_gt; eauto with arith.
        replace (i + S n) with (S (i + n)); auto.
      * rewrite lift_bound_lt; auto with arith.
        rewrite subst_bound_gt; auto with arith.
    + destruct e.
      elim lift_lift_permutation; auto with arith.
      rewrite lift_bound_lt; auto with arith.
      rewrite subst_bound_eq; auto with arith.
    + rewrite lift_bound_lt; auto with arith.
      rewrite lift_bound_lt; auto with arith.
      rewrite subst_bound_lt; auto.
  (* Case: pi. *)
  - simpl; f_equal; auto.
    replace (S (p + k)) with (S p + k); auto.
  (* Case: lambda. *)
  - simpl; f_equal; auto.
    replace (S (p + k)) with (S p + k); auto.
  (* Case: application. *)
  - simpl; f_equal; auto.
Qed.

Lemma lift_distributes_over_subst:
  forall a b i k,
  lift i k (subst b 0 a) = subst (lift i k b) 0 (lift i (S k) a).
Proof.
  intros.
  replace k with (0 + k); auto.
  apply lift_addition_distributes_over_subst.
Qed.

Lemma subst_addition_distributes_over_itself :
  forall a b c p k,
  subst c (p + k) (subst b p a) = subst (subst c k b) p (subst c (S (p + k)) a).
Proof.
  induction a; intros.
  (* Case: type. *)
  - reflexivity.
  (* Case: prop. *)
  - reflexivity.
  (* Case: bound. *)
  - unfold subst at 2.
    destruct (lt_eq_lt_dec p n) as [ [ ? | ? ] | ? ].
    + destruct n.
      inversion l.
      unfold pred, subst at 1.
      destruct (lt_eq_lt_dec (p + k) n) as [ [ ? | ? ] | ? ].
      * rewrite subst_bound_gt; auto with arith.
        rewrite subst_bound_gt; eauto with arith.
      * rewrite subst_bound_eq; auto with arith.
        admit.
      * rewrite subst_bound_lt; eauto with arith.
        rewrite subst_bound_gt; eauto with arith.
    + destruct e.
      rewrite subst_bound_lt; auto with arith.
      rewrite subst_bound_eq; auto.
      admit.
    + rewrite subst_bound_lt; auto with arith.
      rewrite subst_bound_lt; auto with arith.
      rewrite subst_bound_lt; auto with arith.
  (* Case: pi. *)
  - simpl; f_equal; auto.
    replace (S (p + k)) with (S p + k); auto.
  (* Case: lambda. *)
  - simpl; f_equal; auto.
    replace (S (p + k)) with (S p + k); auto.
  (* Case: application. *)
  - simpl; f_equal; auto.
Admitted.

Lemma subst_distributes_over_itself:
  forall a b c k,
  subst c k (subst b 0 a) = subst (subst c k b) 0 (subst c (S k) a).
Proof.
  intros.
  replace k with (0 + k); auto.
  apply subst_addition_distributes_over_itself.
Qed.

(** ** One-step reduction *)

Reserved Notation "[ a => b ]" (at level 0, a at level 99, b at level 99).

Inductive step: pseudoterm -> pseudoterm -> Prop :=
  | step_beta:
    forall t b x,
    [(\t, b) @ x => b[x/]]
  | step_pi_left:
    forall t1 t2 b,
    [t1 => t2] -> [\/t1, b => \/t2, b]
  | step_pi_right:
    forall t b1 b2,
    [b1 => b2] -> [\/t, b1 => \/t, b2]
  | step_lambda_left:
    forall t1 t2 b,
    [t1 => t2] -> [\t1, b => \t2, b]
  | step_lambda_right:
    forall t b1 b2,
    [b1 => b2] -> [\t, b1 => \t, b2]
  | step_application_left:
    forall f1 f2 x,
    [f1 => f2] -> [f1 @ x => f2 @ x]
  | step_application_right:
    forall f x1 x2,
    [x1 => x2] -> [f @ x1 => f @ x2]
where "[ a => b ]" := (step a b): type_scope.

Hint Constructors step: coc.

(** ** Multi-step reduction *)

Definition star: pseudoterm -> pseudoterm -> Prop :=
  clos_refl_trans _ step.

Hint Unfold star: coc.
Hint Constructors clos_refl_trans: coc.
Notation "[ a =>* b ]" := (star a b)
  (at level 0, a at level 99, b at level 99): type_scope.

Lemma star_beta:
  forall t b x,
  [(\t, b) @ x =>* b[x/]].
Proof.
  auto with coc.
Qed.

Hint Resolve star_beta: coc.

Lemma star_step:
  forall a b,
  [a => b] -> [a =>* b].
Proof.
  auto with coc.
Qed.

Hint Resolve star_step: coc.

Lemma star_symm:
  forall a,
  [a =>* a].
Proof.
  auto with coc.
Qed.

Hint Resolve star_symm: coc.

Lemma star_tran:
  forall a b c,
  [a =>* b] -> [b =>* c] -> [a =>* c].
Proof.
  eauto with coc.
Qed.

Hint Resolve star_tran: coc.

Lemma star_pi_left:
  forall t1 t2 b,
  [t1 =>* t2] -> [\/t1, b =>* \/t2, b].
Proof.
  induction 1; eauto with coc.
Qed.

Hint Resolve star_pi_left: coc.

Lemma star_pi_right:
  forall t b1 b2,
  [b1 =>* b2] -> [\/t, b1 =>* \/t, b2].
Proof.
  induction 1; eauto with coc.
Qed.

Hint Resolve star_pi_right: coc.

Lemma star_lambda_left:
  forall t1 t2 b,
  [t1 =>* t2] -> [\t1, b =>* \t2, b].
Proof.
  induction 1; eauto with coc.
Qed.

Hint Resolve star_lambda_left: coc.

Lemma star_lambda_right:
  forall t b1 b2,
  [b1 =>* b2] -> [\t, b1 =>* \t, b2].
Proof.
  induction 1; eauto with coc.
Qed.

Hint Resolve star_lambda_right: coc.

Lemma star_application_left:
  forall f1 f2 x,
  [f1 =>* f2] -> [f1 @ x =>* f2 @ x].
Proof.
  induction 1; eauto with coc.
Qed.

Hint Resolve star_application_left: coc.

Lemma star_application_right:
  forall f x1 x2,
  [x1 =>* x2] -> [f @ x1 =>* f @ x2].
Proof.
  induction 1; eauto with coc.
Qed.

Hint Resolve star_application_right: coc.

(** ** Term conversion *)

Definition conv: pseudoterm -> pseudoterm -> Prop :=
  clos_refl_sym_trans _ step.

Hint Unfold conv: coc.
Hint Constructors clos_refl_sym_trans: coc.
Notation "[ a <=> b ]" := (conv a b)
  (at level 0, a at level 99, b at level 99): type_scope.

Lemma conv_beta:
  forall t b x,
  [(\t, b) @ x <=> b[x/]].
Proof.
  auto with coc.
Qed.

Hint Resolve conv_beta: coc.

Lemma conv_step:
  forall a b,
  [a => b] -> [a <=> b].
Proof.
  auto with coc.
Qed.

Hint Resolve conv_step: coc.

Lemma conv_star:
  forall a b,
  [a =>* b] -> [a <=> b].
Proof.
  induction 1; eauto with coc.
Qed.

Hint Resolve conv_star: coc.

Lemma conv_refl:
  forall a,
  [a <=> a].
Proof.
  auto with coc.
Qed.

Hint Resolve conv_refl: coc.

Lemma conv_tran:
  forall a b c,
  [a <=> b] -> [b <=> c] -> [a <=> c].
Proof.
  eauto with coc.
Qed.

Hint Resolve conv_tran: coc.

Lemma conv_symm:
  forall a b,
  [a <=> b] -> [b <=> a].
Proof.
  auto with coc.
Qed.

Hint Resolve conv_symm: coc.

Lemma conv_pi_left:
  forall t1 t2 b,
  [t1 <=> t2] -> [\/t1, b <=> \/t2, b].
Proof.
  induction 1; eauto with coc.
Qed.

Hint Resolve conv_pi_left: coc.

Lemma conv_pi_right:
  forall t b1 b2,
  [b1 <=> b2] -> [\/t, b1 <=> \/t, b2].
Proof.
  induction 1; eauto with coc.
Qed.

Hint Resolve conv_pi_right: coc.

Lemma conv_lambda_left:
  forall t1 t2 b,
  [t1 <=> t2] -> [\t1, b <=> \t2, b].
Proof.
  induction 1; eauto with coc.
Qed.

Hint Resolve conv_lambda_left: coc.

Lemma conv_lambda_right:
  forall t b1 b2,
  [b1 <=> b2] -> [\t, b1 <=> \t, b2].
Proof.
  induction 1; eauto with coc.
Qed.

Hint Resolve conv_lambda_right: coc.

Lemma conv_application_left:
  forall f1 f2 x,
  [f1 <=> f2] -> [f1 @ x <=> f2 @ x].
Proof.
  induction 1; eauto with coc.
Qed.

Hint Resolve conv_application_left: coc.

Lemma conv_application_right:
  forall f x1 x2,
  [x1 <=> x2] -> [f @ x1 <=> f @ x2].
Proof.
  induction 1; eauto with coc.
Qed.

Hint Resolve conv_application_right: coc.

(******************************************************************************)

Lemma subterm_and_step_commute:
  commut _ subterm (transp _ step).
Proof.
  induction 1; compute; eauto with coc.
Qed.

Hint Unfold transp: coc.

Inductive parallel: pseudoterm -> pseudoterm -> Prop :=
  | parallel_beta:
    forall t b1 b2 x1 x2,
    parallel b1 b2 -> parallel x1 x2 -> parallel ((\t, b1) @ x1) (b2[x2/])
  | parallel_type:
    parallel type type
  | parallel_prop:
    parallel prop prop
  | parallel_bound:
    forall n, parallel (bound n) (bound n)
  | parallel_pi:
    forall t1 t2 b1 b2,
    parallel t1 t2 -> parallel b1 b2 -> parallel (\/t1, b1) (\/t2, b2)
  | parallel_lambda:
    forall t1 t2 b1 b2,
    parallel t1 t2 -> parallel b1 b2 -> parallel (\t1, b1) (\t2, b2)
  | parallel_application:
    forall f1 f2 x1 x2,
    parallel f1 f2 -> parallel x1 x2 -> parallel (f1 @ x1) (f2 @ x2).

Hint Constructors parallel: coc.

Lemma parallel_refl:
  forall e,
  parallel e e.
Proof.
  simple induction e; auto with coc.
Qed.

Hint Resolve parallel_refl: coc.

Lemma parallel_step:
  forall a b,
  [a => b] -> parallel a b.
Proof.
  induction 1; auto with coc.
Qed.

Hint Resolve parallel_step: coc.

Lemma parallel_lift:
  forall a b,
  parallel a b ->
  forall i k,
  parallel (lift i k a) (lift i k b).
Proof.
  simple induction 1.
  (* Case: parallel_beta. *)
  - intros.
    rewrite lift_distributes_over_application.
    rewrite lift_distributes_over_lambda.
    rewrite lift_distributes_over_subst.
    auto with coc.
  (* Case: parallel_type. *)
  - auto with coc.
  (* Case: parallel_prop. *)
  - auto with coc.
  (* Case: parallel_bound. *)
  - auto with coc.
  (* Case: parallel_pi. *)
  - intros.
    do 2 rewrite lift_distributes_over_pi.
    auto with coc.
  (* Case: parallel_lambda. *)
  - intros.
    do 2 rewrite lift_distributes_over_lambda.
    auto with coc.
  (* Case: parallel_application. *)
  - intros.
    do 2 rewrite lift_distributes_over_application.
    auto with coc.
Qed.

Hint Resolve parallel_lift: coc.

Lemma parallel_subst:
  forall a b,
  parallel a b ->
  forall c d,
  parallel c d ->
  forall k,
  parallel (subst c k a) (subst d k b).
Proof.
  simple induction 1.
  (* Case: parallel_beta. *)
  - intros.
    rewrite subst_distributes_over_application.
    rewrite subst_distributes_over_lambda.
    rewrite subst_distributes_over_itself.
    auto with coc.
  (* Case: parallel_type. *)
  - auto with coc.
  (* Case: parallel_prop. *)
  - auto with coc.
  (* Case: parallel_bound. *)
  - intros.
    unfold subst.
    destruct (lt_eq_lt_dec k n) as [ [ ? | ? ] | ? ]; auto with coc.
  (* Case: parallel_pi. *)
  - intros.
    do 2 rewrite subst_distributes_over_pi.
    auto with coc.
  (* Case: parallel_lambda. *)
  - intros.
    do 2 rewrite subst_distributes_over_lambda.
    auto with coc.
  (* Case: parallel_application. *)
  - intros.
    do 2 rewrite subst_distributes_over_application.
    auto with coc.
Qed.

Hint Resolve parallel_subst: coc.

Lemma star_parallel:
  forall a b,
  parallel a b -> [a =>* b].
Proof.
  simple induction 1; intros.
  (* Case: parallel_beta. *)
  - eapply star_tran.
    eapply star_tran.
    apply star_application_left.
    apply star_lambda_right.
    exact H1.
    apply star_application_right.
    exact H3.
    apply star_beta.
  (* Case: parallel_type. *)
  - auto with coc.
  (* Case: parallel_prop. *)
  - auto with coc.
  (* Case: parallel_bound. *)
  - auto with coc.
  (* Case: parallel_pi. *)
  - eauto with coc.
  (* Case: parallel_lambda. *)
  - eauto with coc.
  (* Case: parallel_application. *)
  - eauto with coc.
Qed.

Hint Resolve star_parallel: coc.

Lemma star_subst_left:
  forall b1 b2,
  [b1 =>* b2] ->
  forall x,
  [b1[x/] =>* b2[x/]].
Proof.
  intros until 1.
  dependent induction H; eauto with coc.
Qed.

Hint Resolve star_subst_left: coc.

Lemma star_subst_right:
  forall x1 x2,
  [x1 =>* x2] ->
  forall b,
  [b[x1/] =>* b[x2/]].
Proof.
  intros until 1.
  dependent induction H; eauto with coc.
Qed.

Hint Resolve star_subst_right: coc.

Lemma star_subst:
  forall b1 b2,
  [b1 =>* b2] ->
  forall x1 x2,
  [x1 =>* x2] -> [b1[x1/] =>* b2[x2/]].
Proof.
  eauto with coc.
Qed.

Hint Resolve star_subst: coc.

Lemma conv_subst_left:
  forall b1 b2,
  [b1 <=> b2] ->
  forall x,
  [b1[x/] <=> b2[x/]].
Proof.
  intros until 1.
  dependent induction H; eauto with coc.
Qed.

Hint Resolve conv_subst_left: coc.

Lemma conv_subst_right:
  forall x1 x2,
  [x1 <=> x2] ->
  forall b,
  [b[x1/] <=> b[x2/]].
Proof.
  intros until 1.
  dependent induction H; eauto with coc.
Qed.

Hint Resolve conv_subst_right: coc.

Lemma conv_subst:
  forall b1 b2,
  [b1 <=> b2] ->
  forall x1 x2,
  [x1 <=> x2] -> [b1[x1/] <=> b2[x2/]].
Proof.
  eauto with coc.
Qed.

Hint Resolve conv_subst: coc.

(******************************************************************************)
(*     __  __ ______  _____ _______     __    _____ ____  _____  ______ _     *)
(*    |  \/  |  ____|/ ____/ ____\ \   / /   / ____/ __ \|  __ \|  ____| |    *)
(*    | \  / | |__  | (___| (___  \ \_/ /   | |   | |  | | |  | | |__  | |    *)
(*    | |\/| |  __|  \___ \\___ \  \   /    | |   | |  | | |  | |  __| | |    *)
(*    | |  | | |____ ____) |___) |  | |     | |___| |__| | |__| | |____|_|    *)
(*    |_|  |_|______|_____/_____/   |_|      \_____\____/|_____/|______(_)    *)
(*                                                                            *)
(******************************************************************************)

Definition confluent {T} (R: T -> T -> Prop): Prop :=
  commut _ R (transp _ R).

Lemma parallel_is_confluent:
  confluent parallel.
Proof.
  compute.
  induction 1.
  (* Case: parallel_beta. *)
  - intros.
    inversion_clear H1.
    + destruct (IHparallel1 _ H2) as (b4, ?, ?).
      destruct (IHparallel2 _ H3) as (x4, ?, ?).
      exists (subst x4 0 b4); auto with coc.
    + inversion_clear H2.
      destruct (IHparallel1 _ H4) as (b4, ?, ?).
      destruct (IHparallel2 _ H3) as (x4, ?, ?).
      exists (subst x4 0 b4); auto with coc.
  (* Case: parallel_type. *)
  - intros.
    inversion_clear H.
    exists type; auto with coc.
  (* Case: parallel_prop. *)
  - intros.
    inversion_clear H.
    exists prop; auto with coc.
  (* Case: parallel_bound. *)
  - intros.
    inversion_clear H.
    exists n; auto with coc.
  (* Case: parallel_pi. *)
  - intros.
    inversion_clear H1.
    destruct (IHparallel1 _ H2) as (t4, ?, ?).
    destruct (IHparallel2 _ H3) as (b4, ?, ?).
    exists (pi t4 b4); auto with coc.
  (* Case: parallel_lambda. *)
  - intros.
    inversion_clear H1.
    destruct (IHparallel1 _ H2) as (t4, ?, ?).
    destruct (IHparallel2 _ H3) as (b4, ?, ?).
    exists (lambda t4 b4); auto with coc.
  (* Case: parallel_application. *)
  - intros.
    inversion H1.
    + destruct H3, H2, H5.
      rename t into t1, x0 into x1, b2 into b3.
      inversion H.
      destruct H2, H3, H7.
      rename t0 into t1, b0 into b1.
      edestruct IHparallel1.
      apply parallel_lambda.
      apply parallel_refl.
      exact H4.
      rename x into f4.
      inversion H2.
      destruct H7, H9, H11.
      rename t0 into t2, b0 into b2.
      inversion H3.
      destruct H7, H9, H11, H14.
      rename t0 into t1, b0 into b3, b5 into b4.
      destruct (IHparallel2 _ H6) as (x4, ?, ?).
      exists (subst x4 0 b4); eauto with coc.
    + destruct H2, H3, H5.
      destruct (IHparallel1 _ H4) as (f4, ?, ?).
      destruct (IHparallel2 _ H6) as (x4, ?, ?).
      exists (application f4 x4); auto with coc.
Qed.

Lemma strip_lemma {T} (R: T -> T -> Prop):
  confluent R -> commut _ (clos_trans _ R) (transp _ R).
Proof.
  simple induction 2; intros.
  - elim H with z x0 y0; eauto with sets.
  - elim H2 with z0; auto with sets; intros.
    elim H4 with x1; auto with sets; intros.
    eexists; eauto with sets.
    eapply t_trans; eauto.
Qed.

Lemma transitive_closure_of_confluent_is_confluent {T} (R: T -> T -> Prop):
  confluent R -> confluent (clos_trans _ R).
Proof.
  intro confluency.
  unfold confluent, commut, transp.
  simple induction 1; intros.
  destruct (strip_lemma R) with z x0 y0; auto.
  - eauto with sets.
  - elim H1 with z0; auto; intros.
    elim H3 with x1; auto; intros.
    exists x2; auto.
    eapply t_trans; eauto.
Qed.

Lemma transitive_parallel_is_confluent:
  confluent (clos_trans _ parallel).
Proof.
  apply transitive_closure_of_confluent_is_confluent.
  exact parallel_is_confluent.
Qed.

Lemma transitive_parallel_star:
  forall a b,
  [a =>* b] -> clos_trans _ parallel a b.
Proof.
  simple induction 1.
  - auto with coc sets.
  - auto with coc sets.
  - intros; eapply t_trans; eauto.
Qed.

Lemma star_transitive_parallel:
  forall a b,
  clos_trans _ parallel a b -> [a =>* b].
Proof.
  induction 1; eauto with coc.
Qed.

Lemma star_is_confluent:
  confluent star.
Proof.
  unfold confluent, commut, transp.
  intros.
  elim transitive_parallel_is_confluent with x y z.
  - compute; intros.
    exists x0.
    apply star_transitive_parallel; auto.
    apply star_transitive_parallel; auto.
  - eapply transitive_parallel_star; auto.
  - eapply transitive_parallel_star; auto.
Qed.

Definition church_rosser {T} (R: T -> T -> Prop): Prop :=
  forall a b,
  clos_refl_sym_trans T R a b ->
  exists2 c: T, clos_refl_trans T R a c & clos_refl_trans T R b c.

Lemma confluency_implies_church_rosser {T} (R: T -> T -> Prop):
  confluent (clos_refl_trans _ R) -> church_rosser R.
Proof.
  simple induction 2; intros.
  - eauto with sets.
  - eauto with sets.
  - destruct H2 as (z, ?, ?).
    exists z; auto.
  - destruct H2 as (c, ?, ?).
    destruct H4 as (d, ?, ?).
    destruct H with c y d as (e, ?, ?); auto.
    exists e; eapply rt_trans; eauto.
Qed.

Theorem step_is_church_rosser:
  church_rosser step.
Proof.
  apply confluency_implies_church_rosser.
  exact star_is_confluent.
Qed.

(******************************************************************************)

Lemma inversion_star_pi:
  forall t b x,
  [\/t, b =>* x] ->
  exists2 t2, [t =>* t2] &
    exists2 b2, [b =>* b2] & x = pi t2 b2.
Proof.
  intros until 1.
  dependent induction H.
  (* Case: step. *)
  - inversion_clear H.
    + exists t2; auto with coc.
      exists b; auto with coc.
    + exists t; auto with coc.
      exists b2; auto with coc.
  (* Case: refl. *)
  - exists t; auto with coc.
    exists b; auto with coc.
  (* Case: tran. *)
  - destruct IHclos_refl_trans1 with t b; auto.
    destruct H2.
    destruct IHclos_refl_trans2 with x x0; auto.
    destruct H5.
    exists x1.
    eauto with coc.
    exists x2.
    eauto with coc.
    assumption.
Qed.

Lemma inversion_conv_pi:
  forall t b t2 b2,
  [\/t, b <=> \/t2, b2] -> [t <=> t2] /\ [b <=> b2].
Proof.
  intros.
  elim step_is_church_rosser with (pi t b) (pi t2 b2); fold star conv.
  - intros.
    destruct inversion_star_pi with t b x; auto.
    destruct H3, (eq_sym H4); clear H4.
    destruct inversion_star_pi with t2 b2 (pi x0 x1); auto.
    destruct H5.
    inversion H6; destruct H8, H9.
    split; eauto with coc.
  - assumption.
Qed.

Hint Resolve inversion_conv_pi: coc.

Lemma step_lift:
  forall a b,
  [a => b] ->
  forall i k,
  [lift i k a => lift i k b].
Proof.
  induction 1; intros.
  - rewrite lift_distributes_over_subst.
    apply step_beta.
  - apply step_pi_left; auto.
  - apply step_pi_right; auto.
  - apply step_lambda_left; auto.
  - apply step_lambda_right; auto.
  - apply step_application_left; auto.
  - apply step_application_right; auto.
Qed.

Hint Resolve step_lift: coc.

Lemma star_lift:
  forall a b,
  [a =>* b] ->
  forall i k,
  [lift i k a =>* lift i k b].
Proof.
  induction 1; eauto with coc.
Qed.

Hint Resolve star_lift: coc.

Lemma conv_lift:
  forall a b,
  [a <=> b] ->
  forall i k,
  [lift i k a <=> lift i k b].
Proof.
  induction 1; eauto with coc.
Qed.

Hint Resolve conv_lift: coc.

(******************************************************************************)

Definition normal (a: pseudoterm): Prop :=
  forall b, ~[a => b].

Definition strongly_normalizing: pseudoterm -> Prop :=
  Acc (transp _ step).

Lemma subterm_of_normalizing_is_normalizing:
  forall a,
  strongly_normalizing a ->
  forall b,
  subterm b a -> strongly_normalizing b.
Proof.
  compute.
  simple induction 1.
  intros.
  constructor.
  intros.
  edestruct subterm_and_step_commute; eauto.
Qed.

Lemma inversion_star_normal:
  forall a b,
  [a =>* b] -> normal a ->
  forall P: Prop,
  (a = b -> P) -> P.
Proof.
  simple induction 1; intros.
  (* Case: step. *)
  - absurd (step x y); auto.
  (* Case: refl. *)
  - auto.
  (* Case: tran. *)
  - apply H1.
    assumption.
    intro.
    destruct H6.
    apply H3; auto.
Qed.

Lemma normal_form_is_unique:
  forall a b,
  [a <=> b] -> normal a -> normal b -> a = b.
Proof.
  intros.
  destruct step_is_church_rosser with a b.
  - assumption.
  - apply inversion_star_normal with a x;
      apply inversion_star_normal with b x;
      auto.
    congruence.
Qed.

(******************************************************************************)

Definition context: Set :=
  list pseudoterm.

Bind Scope list_scope with context.

Inductive item (e: pseudoterm): context -> nat -> Prop :=
  | item_car:
    forall cdr, item e (cons e cdr) 0
  | item_cdr:
    forall car cdr n, item e cdr n -> item e (cons car cdr) (S n).

Hint Constructors item: coc.

Definition item_lift (e: pseudoterm) (g: context) (n: nat): Prop :=
  exists2 x, e = lift (S n) 0 x & item x g n.

Lemma item_lift_unique:
  forall a b g n,
  item_lift a g n -> item_lift b g n -> a = b.
Proof.
  intros.
  destruct H, H0.
  rewrite H, H0; clear H H0.
  generalize n.
  induction H1.
  - inversion H2.
    reflexivity.
  - inversion_clear H2.
    eauto.
Qed.

Reserved Notation "[ g |- e : t ]"
  (at level 0, g at level 99, e at level 99, t at level 99,
   format "[ g  |-  e :  t ]").

Inductive typing: context -> pseudoterm -> pseudoterm -> Prop :=
  | typing_prop:
    forall g, valid_context g -> [g |- prop: type]
  | typing_bound:
    forall g, valid_context g ->
    forall n t, item_lift t g n -> [g |- n: t]
  | typing_pi1:
    forall g t b,
    [g |- t: type] -> [t :: g |- b: type] -> [g |- \/t, b: type]
  | typing_pi2:
    forall g t b,
    [g |- t: prop] -> [t :: g |- b: type] -> [g |- \/t, b: type]
  | typing_pi3:
    forall g t b,
    [g |- t: type] -> [t :: g |- b: prop] -> [g |- \/t, b: prop]
  | typing_pi4:
    forall g t b,
    [g |- t: prop] -> [t :: g |- b: prop] -> [g |- \/t, b: prop]
  | typing_lambda1:
    forall g e t u,
    [g |- t: type] -> [t :: g |- u: type] -> [t :: g |- e: u] ->
    [g |- \t, e: \/t, u]
  | typing_lambda2:
    forall g e t u,
    [g |- t: prop] -> [t :: g |- u: type] -> [t :: g |- e: u] ->
    [g |- \t, e: \/t, u]
  | typing_lambda3:
    forall g e t u,
    [g |- t: type] -> [t :: g |- u: prop] -> [t :: g |- e: u] ->
    [g |- \t, e: \/t, u]
  | typing_lambda4:
    forall g e t u,
    [g |- t: prop] -> [t :: g |- u: prop] -> [t :: g |- e: u] ->
    [g |- \t, e: \/t, u]
  | typing_application:
    forall g f x t b,
    [g |- f: \/t, b] -> [g |- x: t] -> [g |- f @ x: b[x/]]
  | typing_conv:
    forall g e t1 t2,
    [g |- e: t1] -> [t1 <=> t2] -> [g |- e: t2]
with valid_context: context -> Prop :=
  | valid_context_nil:
    valid_context nil
  | valid_context_type_var:
    forall g t, [g |- t: type] -> valid_context (cons t g)
  | valid_context_term_var:
    forall g t, [g |- t: prop] -> valid_context (cons t g)
where "[ g |- e : t ]" := (typing g e t): type_scope.

Hint Constructors typing: coc.
Hint Constructors valid_context: coc.

Lemma typing_valid_context:
  forall g e t,
  typing g e t -> valid_context g.
Proof.
  induction 1; assumption.
Qed.

Hint Resolve typing_valid_context: coc.

Lemma inversion_typing_type:
  forall g t,
  ~[g |- type: t].
Proof.
  intros until 1.
  dependent induction H; auto.
Qed.

Lemma inversion_typing_prop:
  forall g t,
  [g |- prop: t] -> [t <=> type].
Proof.
  intros until 1.
  dependent induction H; eauto with coc.
Qed.

Lemma inversion_typing_bound:
  forall g t (n: nat),
  [g |- n: t] ->
  exists2 x, item_lift x g n & [t <=> x].
Proof.
  intros until 1.
  dependent induction H.
  - exists t; eauto with coc.
  - destruct IHtyping with n; auto.
    exists x; eauto with coc.
Qed.

Lemma inversion_typing_pi:
  forall g t b s,
  [g |- \/t, b: s] ->
  exists2 s2, [g |- t: s2] & [t :: g |- b: s].
Proof.
  intros until 1.
  dependent induction H.
  - eauto with coc.
  - eauto with coc.
  - eauto with coc.
  - eauto with coc.
  - destruct IHtyping with t b; auto.
    eexists; eauto.
    eapply typing_conv; eauto.
Qed.

Lemma inversion_typing_lambda:
  forall g t2 b t,
  [g |- \t2, b: t] ->
  exists2 s1, [g |- t2: s1] &
    exists2 u, [t2 :: g |- b: u] &
      exists2 s2, [t2 :: g |- u: s2] & [t <=> \/t2, u].
Proof.
  intros until 1.
  dependent induction H.
  - eauto with coc.
  - eauto with coc.
  - eauto with coc.
  - eauto with coc.
  - destruct IHtyping with t2 b; auto.
    eexists; eauto.
    destruct H2.
    eexists; eauto.
    destruct H3.
    eexists; eauto with coc.
Qed.

Lemma inversion_typing_application:
  forall g f x t,
  [g |- f @ x: t] ->
  exists2 t2, [g |- x: t2] &
    exists2 b, [g |- f: \/t2, b] & [t <=> b[x/]].
Proof.
  intros until 1.
  dependent induction H.
  - exists t; auto.
    exists b; eauto with coc.
  - destruct IHtyping with f x; auto.
    eexists; eauto.
    destruct H2.
    eexists; eauto with coc.
Qed.

Inductive insert x: nat -> context -> context -> Prop :=
  | insert_car:
    forall cdr, insert x 0 cdr (x :: cdr)
  | insert_cdr:
    forall n car cdr res,
    insert x n cdr res -> insert x (S n) (car :: cdr) (lift 1 n car :: res).

Hint Constructors insert: coc.

Lemma typing_weak_lift:
  forall g e t,
  [g |- e: t] ->
  forall x n h,
  insert x n g h -> valid_context h -> [h |- lift 1 n e: lift 1 n t].
Proof.
  intros until 1.
  dependent induction H; intros.
  - apply typing_prop; auto.
  - destruct H0; rewrite H0; clear H0.
    rename x0 into y.
    dependent induction H1.
    + simpl.
      apply typing_bound; auto.
      exists y; auto with coc.
      rewrite lift_i_lift_j_equals_lift_i_plus_j; auto.
    + rename n0 into m.
      unfold lift at 2.
      destruct (le_gt_dec (S m) n).
      * admit.
      * admit.
  - apply typing_pi1; eauto with coc.
  - apply typing_pi2; eauto with coc.
  - apply typing_pi3; eauto with coc.
  - apply typing_pi4; eauto with coc.
  - apply typing_lambda1; eauto with coc.
  - apply typing_lambda2; eauto with coc.
  - apply typing_lambda3; eauto with coc.
  - apply typing_lambda4; eauto with coc.
  - simpl in * |- *.
    rewrite lift_distributes_over_subst.
    simple eapply typing_application; eauto with coc.
  - eapply typing_conv; eauto with coc.
Admitted.

Theorem weakening:
  forall g e t,
  [g |- e: t] ->
  forall x,
  valid_context (x :: g) -> [x :: g |- lift 1 0 e: lift 1 0 t].
Proof.
  intros.
  eapply typing_weak_lift; eauto with coc.
Qed.

Hint Resolve weakening: coc.

Theorem typing_subst:
  forall e t u U d,
  [t :: e |- u: U] -> [e |- d: t] -> [e |- u[d/]: U[d/]].
Proof.
Admitted.

Hint Resolve typing_subst: coc.

Theorem typing_unique_up_to_conv:
  forall g e t1,
  [g |- e: t1] ->
  forall t2,
  [g |- e: t2] -> [t1 <=> t2].
Proof.
  induction 1; intros.
  (* Case: typing_prop. *)
  - apply conv_symm.
    apply inversion_typing_prop with g.
    auto.
  (* Case: typing_bound. *)
  - edestruct inversion_typing_bound; eauto.
    destruct item_lift_unique with t x g n; auto.
    apply conv_symm; auto.
  (* Case: typing_pi1. *)
  - destruct inversion_typing_pi with g t b t2; auto.
  (* Case: typing_pi2. *)
  - destruct inversion_typing_pi with g t b t2; auto.
  (* Case: typing_pi3. *)
  - destruct inversion_typing_pi with g t b t2; auto.
  (* Case: typing_pi4. *)
  - destruct inversion_typing_pi with g t b t2; auto.
  (* Case: typing_lambda1. *)
  - destruct inversion_typing_lambda with g t e t2; auto.
    destruct H4; destruct H5.
    eapply conv_tran.
    apply conv_pi_right.
    apply IHtyping3; eauto.
    apply conv_symm; auto.
  (* Case: typing_lambda2. *)
  - destruct inversion_typing_lambda with g t e t2; auto.
    destruct H4; destruct H5.
    eapply conv_tran.
    apply conv_pi_right.
    apply IHtyping3; eauto.
    apply conv_symm; auto.
  (* Case: typing_lambda3. *)
  - destruct inversion_typing_lambda with g t e t2; auto.
    destruct H4; destruct H5.
    eapply conv_tran.
    apply conv_pi_right.
    apply IHtyping3; eauto.
    apply conv_symm; auto.
  (* Case: typing_lambda4. *)
  - destruct inversion_typing_lambda with g t e t2; auto.
    destruct H4; destruct H5.
    eapply conv_tran.
    apply conv_pi_right.
    apply IHtyping3; eauto.
    apply conv_symm; auto.
  (* Case: typing_application. *)
  - destruct inversion_typing_application with g f x t2; auto.
    destruct H3.
    apply conv_symm.
    eapply conv_tran; eauto.
    apply conv_subst_left.
    eapply inversion_conv_pi.
    apply conv_symm.
    apply IHtyping1.
    eassumption.
  (* Case: typing_conv. *)
  - eauto with coc.
Qed.

Hint Resolve typing_unique_up_to_conv: coc.

Lemma lift_succ_n_equals_lift_1_lift_n:
  forall n k e,
  lift (S n) k e = lift 1 k (lift n k e).
Proof.
  intros.
  replace (S n) with (1 + n); auto.
  rewrite lift_i_lift_j_equals_lift_i_plus_j; auto.
Qed.

Lemma well_founded_lift_has_sort:
  forall n g t,
  valid_context g -> item_lift t g n -> [g |- t: prop] \/ [g |- t: type].
Proof.
  induction n; intros.
  (* Case: zero. *)
  - destruct g; destruct H0.
    + inversion H1.
    + rewrite H0; clear H0.
      inversion_clear H; inversion_clear H1.
      * right; replace type with (lift 1 0 type); eauto with coc.
      * left; replace prop with (lift 1 0 prop); eauto with coc.
  (* Case: succ. *)
  - destruct H0.
    rewrite H0; clear H0.
    inversion H1.
    destruct H2.
    clear n0 H0.
    rewrite lift_succ_n_equals_lift_1_lift_n.
    replace prop with (lift 1 0 prop); auto.
    replace type with (lift 1 0 type); auto.
    destruct IHn with cdr (lift (S n) 0 x).
    + inversion H; eauto with coc.
    + exists x; auto.
    + left; apply weakening; auto.
    + right; apply weakening; auto.
Qed.

Lemma typing_case:
  forall g e t,
  [g |- e: t] -> t = type \/ [g |- t: prop] \/ [g |- t: type].
Proof.
  intros until 1.
  dependent induction H.
  (* Case: typing_prop. *)
  - auto.
  (* Case: typing_bound. *)
  - right.
    apply well_founded_lift_has_sort with n; auto.
  (* Case: typing_pi1. *)
  - auto.
  (* Case: typing_pi2. *)
  - auto.
  (* Case: typing_pi3. *)
  - eauto with coc.
  (* Case: typing_pi4. *)
  - eauto with coc.
  (* Case: typing_lambda1. *)
  - eauto with coc.
  (* Case: typing_lambda2. *)
  - eauto with coc.
  (* Case: typing_lambda3. *)
  - eauto with coc.
  (* Case: typing_lambda4. *)
  - eauto with coc.
  (* Case: typing_application. *)
  - admit.
  (* Case: typing_conv. *)
  - (* Huh... we need subject reduction... *)
    admit.
Admitted.

(******************************************************************************)

Inductive context_step: context -> context -> Prop :=
  | context_step_car:
    forall g t u,
    [t => u] -> context_step (t :: g) (u :: g)
  | context_step_cdr:
    forall g h t,
    context_step g h -> context_step (t :: g) (t :: h).

Hint Constructors context_step: coc.

Lemma typing_preserved_under_context_step:
  forall g e t,
  [g |- e: t] ->
  forall h,
  context_step g h -> valid_context h -> [h |- e: t].
Proof.
  intros until 1.
  dependent induction H; intros.
  (* Case: typing_prop. *)
  - auto with coc.
  (* Case: typing_bound. *)
  - admit.
  (* Case: typing_pi1. *)
  - admit.
  (* Case: typing_pi2. *)
  - admit.
  (* Case: typing_pi3. *)
  - admit.
  (* Case: typing_pi4. *)
  - admit.
  (* Case: typing_lambda1. *)
  - admit.
  (* Case: typing_lambda2. *)
  - admit.
  (* Case: typing_lambda3. *)
  - admit.
  (* Case: typing_lambda4. *)
  - admit.
  (* Case: typing_application. *)
  - admit.
  (* Case: typing_conv. *)
  - apply typing_conv with t1; auto.
Admitted.

Hint Resolve typing_preserved_under_context_step: coc.

Lemma inversion_typing_lambda_body:
  forall g t1 e x,
  [g |- \t1, e: x] ->
  forall b,
  [x <=> \/t1, b] -> [t1 :: g |- e: b].
Proof.
  intros until 1.
  dependent induction H; intros.
  - edestruct inversion_conv_pi; eauto with coc.
  - edestruct inversion_conv_pi; eauto with coc.
  - edestruct inversion_conv_pi; eauto with coc.
  - edestruct inversion_conv_pi; eauto with coc.
  - eauto with coc.
Qed.

Hint Resolve inversion_typing_lambda_body: coc.

Lemma typing_preserved_under_step:
  forall g e1 t,
  [g |- e1: t] ->
  forall e2,
  [e1 => e2] -> [g |- e2: t].
Proof.
  intros until 1.
  dependent induction H; intros.
  (* Case: typing_prop. *)
  - inversion H0; auto.
  (* Case: typing_bound. *)
  - inversion H1.
  (* Case: typing_pi1. *)
  - inversion_clear H1.
    + apply typing_pi1; eauto with coc.
    + apply typing_pi1; eauto with coc.
  (* Case: typing_pi2. *)
  - inversion_clear H1.
    + apply typing_pi2; eauto with coc.
    + apply typing_pi2; eauto with coc.
  (* Case: typing_pi3. *)
  - inversion_clear H1.
    + apply typing_pi3; eauto with coc.
    + apply typing_pi3; eauto with coc.
  (* Case: typing_pi4. *)
  - inversion_clear H1.
    + apply typing_pi4; eauto with coc.
    + apply typing_pi4; eauto with coc.
  (* Case: typing_lambda1. *)
  - inversion_clear H2.
    + apply typing_conv with (pi t2 u).
      apply typing_lambda1; eauto with coc.
      eauto with coc.
    + apply typing_lambda1; auto.
  (* Case: typing_lambda2. *)
  - inversion_clear H2.
    + apply typing_conv with (pi t2 u).
      apply typing_lambda2; eauto with coc.
      eauto with coc.
    + apply typing_lambda2; auto.
  (* Case: typing_lambda3. *)
  - inversion_clear H2.
    + apply typing_conv with (pi t2 u).
      apply typing_lambda3; eauto with coc.
      eauto with coc.
    + apply typing_lambda3; auto.
  (* Case: typing_lambda4. *)
  - inversion_clear H2.
    + apply typing_conv with (pi t2 u).
      apply typing_lambda4; eauto with coc.
      eauto with coc.
    + apply typing_lambda4; auto.
  (* Case: typing_application. *)
  - inversion H1.
    + destruct H2, H3, (eq_sym H4); clear H4.
      edestruct inversion_typing_lambda.
      exact H.
      destruct H3.
      destruct H4.
      edestruct inversion_conv_pi.
      exact H5.
      apply typing_subst with t0; auto.
      eapply inversion_typing_lambda_body.
      exact H.
      eauto with coc.
      eauto with coc.
    + apply typing_application with t; auto.
    + apply typing_conv with (subst x2 0 b); eauto with coc.
  (* Case: typing_conv. *)
  - eauto with coc.
Qed.

Hint Resolve typing_preserved_under_step: coc.

Theorem subject_reduction:
  forall e1 e2,
  [e1 =>* e2] ->
  forall g t,
  [g |- e1: t] -> [g |- e2: t].
Proof.
  simple induction 1; eauto with coc.
Qed.
