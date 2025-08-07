import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Order.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Tactic.Linarith.Frontend
open Lean PrettyPrinter Delaborator SubExpr

-- inductive example_type : Type 1
--   | A | B | C
--   deriving DecidableEq

def castByEq {A B} (a : A) (h : A = B) : B :=
  Eq.mp h a

infixl:60 " ◂ " => castByEq

inductive Variable where
  | var (n : ℕ) : Variable
  deriving DecidableEq

inductive Predicate (arity : ℕ) where
  | pred (n : ℕ) : Predicate arity
  deriving DecidableEq

inductive Formula where
  | predicate {arity : ℕ} (p : Predicate arity) (args : Vector Variable arity) : Formula
  | not (φ : Formula ): Formula
  | and (φ ψ : Formula) : Formula
  | or (φ ψ : Formula) : Formula
  | implies (φ ψ : Formula) : Formula
  | all (x : Variable) (φ : Formula) : Formula
  | exists' (x : Variable) (φ : Formula) : Formula
  deriving DecidableEq

declare_syntax_cat formula_args
syntax ident              : formula_args
syntax ident formula_args : formula_args

declare_syntax_cat formula_predicate
syntax ident "(" ")"               : formula_predicate
syntax ident "(" formula_args ")"  : formula_predicate

declare_syntax_cat formula
syntax:10 formula_predicate           : formula
syntax:20 formula:21 " → " formula:20 : formula
syntax:30 formula:30 " ∨ " formula:31 : formula
syntax:30 formula:30 " ∧ " formula:31 : formula
syntax:40 "¬" formula:40              : formula
syntax:50 "∀" ident formula:50        : formula
syntax:50 "∃" ident formula:50        : formula
syntax ident                          : formula
syntax "(" formula ")"                : formula
syntax "⟪" formula "⟫"                : term
syntax "!⟪" formula_args "⟫!"         : term

macro_rules
  | `(⟪ $φ:formula → $ψ:formula ⟫) => `(Formula.implies ⟪ $φ ⟫ ⟪ $ψ ⟫)
  | `(⟪ $φ:formula ∨ $ψ:formula ⟫) => `(Formula.or ⟪ $φ ⟫ ⟪ $ψ ⟫)
  | `(⟪ $φ:formula ∧ $ψ:formula ⟫) => `(Formula.and ⟪ $φ ⟫ ⟪ $ψ ⟫)
  | `(⟪ ¬$φ:formula ⟫) => `(Formula.not ⟪ $φ ⟫)
  | `(⟪ ($φ:formula) ⟫) => `(⟪ $φ ⟫)
  | `(⟪ $φ:ident ⟫) => `($φ)
  | `(⟪ ∀$x:ident $φ:formula ⟫) => `(Formula.all $x ⟪$φ⟫)
  | `(⟪ ∃$x:ident $φ:formula ⟫) => `(Formula.exists' $x ⟪$φ⟫)
  | `(⟪ $P:ident() ⟫) => `(Formula.predicate (arity:=0) $P _)
  | `(⟪ $P:ident ($xs:ident) ⟫) => `(Formula.predicate $P $xs)
  | `(⟪ $P:ident ($xs:formula_args) ⟫) => `(Formula.predicate $P !⟪$xs⟫!)
  | `(!⟪ $x:ident $ys:formula_args ⟫!) => `($x ::ᵥ !⟪$ys⟫!)
  | `(!⟪ $x:ident ⟫!) => `(Vector.singleton $x)

/- InfoView niceities -/
@[app_unexpander Formula.implies]
def unexpandImplies : Unexpander
  | `($_ $φ $ψ) => `($φ → $ψ)
  | _ => throw ()
@[app_unexpander Formula.and]
def unexpandAnd : Unexpander
  | `($_ $φ $ψ) => `($φ ∧ $ψ)
  | _ => throw ()
@[app_unexpander Formula.or]
def unexpandOr : Unexpander
  | `($_ $φ $ψ) => `($φ ∨ $ψ)
  | _ => throw ()
@[app_unexpander Formula.not]
def unexpandNot : Unexpander
  | `($_ $φ) => `(¬$φ)
  | _ => throw ()




inductive FreeIn (var : Variable) : Formula → Prop where
  | predicate {p args} : FreeIn var ⟪p (args)⟫
  | not {φ} : FreeIn var φ → FreeIn var ⟪¬φ⟫
  | and₁ {φ ψ} : FreeIn var φ → FreeIn var ⟪φ ∧ ψ⟫
  | and₂ {φ ψ} : FreeIn var ψ → FreeIn var ⟪φ ∧ ψ⟫
  | or₁ {φ ψ} : FreeIn var φ → FreeIn var ⟪φ ∨ ψ⟫
  | or₂ {φ ψ} : FreeIn var ψ → FreeIn var ⟪φ ∨ ψ⟫
  | implies₁ {φ ψ} : FreeIn var φ → FreeIn var ⟪φ → ψ⟫
  | implies₂ {φ ψ} : FreeIn var ψ → FreeIn var ⟪φ → ψ⟫
  | all {φ x} : FreeIn var φ → x ≠ var → FreeIn var ⟪∀x φ⟫
  | exists' {φ x} : FreeIn var φ → x ≠ var → FreeIn var ⟪∃x φ⟫

inductive OccursIn (var : Variable) : Formula → Prop where
  | predicate {p args} : var ∈ args → OccursIn var ⟪p (args)⟫
  | not {φ} : OccursIn var φ → OccursIn var ⟪¬φ⟫
  | and₁ {φ ψ} : OccursIn var φ → OccursIn var ⟪φ ∧ ψ⟫
  | and₂ {φ ψ} : OccursIn var ψ → OccursIn var ⟪φ ∧ ψ⟫
  | or₁ {φ ψ} : OccursIn var φ → OccursIn var ⟪φ ∨ ψ⟫
  | or₂ {φ ψ} : OccursIn var ψ → OccursIn var ⟪φ ∨ ψ⟫
  | implies₁ {φ ψ} : OccursIn var φ → OccursIn var ⟪φ → ψ⟫
  | implies₂ {φ ψ} : OccursIn var ψ → OccursIn var ⟪φ → ψ⟫
  | all₁ {φ x} : OccursIn var φ → OccursIn var ⟪∀x φ⟫
  | all₂ {φ x} : x = var → OccursIn var ⟪∀x φ⟫
  | exists'₁ {φ x} : OccursIn var φ → OccursIn var ⟪∃x φ⟫
  | exists'₂ {φ x} : x = var → OccursIn var ⟪∃x φ⟫

def BoundIn (var : Variable) (φ : Formula) : Prop := ¬FreeIn var φ ∧ OccursIn var φ

def FreeAmong (φ : Formula) (vars : List Variable) : Prop := ∀ var ∈ vars, FreeIn var φ

def FreeForIn (x y : Variable) (φ : Formula) : Prop := sorry

def Axiom : Type := (numFreeVars : ℕ) × (Vector Formula numFreeVars → Formula)

def Rule : Type := (numFreeVars : ℕ) × (Vector Formula numFreeVars → (List Formula × Formula))

/-
inductive MetaRule where
  | metaRule : List Formula → Consequence → Consequence → MetaRule
-/


-- What is a logic?
-- A logic is a collection of Axioms and Rules (and Meta-Rules)
structure Logic where
  axioms : List Axiom
  rules : List Rule

-- Axioms
def A1 : Axiom  := ⟨1, fun xs ↦ let A := xs[0];
                       ⟪A → A⟫⟩
def A2 : Axiom  := ⟨2, fun xs ↦ let (A, B) := (xs[0], xs[1]);
                       ⟪A ∧ B → A⟫⟩
def A3 : Axiom  := ⟨2, fun xs ↦ let (A, B) := (xs[0], xs[1]);
                       ⟪A ∧ B → B⟫⟩
def A4 : Axiom  := ⟨3, fun xs ↦ let (A, B, C) := (xs[0], xs[1], xs[2]);
                       ⟪((A → B) ∧ (A → C)) → (A → (B ∧ C))⟫⟩
def A5 : Axiom  := ⟨2, fun xs ↦ let (A, B) := (xs[0], xs[1]);
                       ⟪A → (A ∨ B)⟫⟩
def A6 : Axiom  := ⟨2, fun xs ↦ let (A, B) := (xs[0], xs[1]);
                       ⟪B → (A ∨ B)⟫⟩
def A7 : Axiom  := ⟨3, fun xs ↦ let (A, B, C) := (xs[0], xs[1], xs[2]);
                       ⟪((A → C) ∧ (B → C)) → ((A ∨ B) → C)⟫⟩
def A8 : Axiom  := ⟨3, fun xs ↦ let (A, B, C) := (xs[0], xs[1], xs[2]);
                       ⟪(A ∧ (B ∨ C)) → ((A ∧ B) ∨ (A ∧ C))⟫⟩
def A9 : Axiom  := ⟨1, fun xs ↦ let A := xs[0];
                       ⟪¬¬A → A⟫⟩
def A10 : Axiom := ⟨2, fun xs ↦ let (A, B) := (xs[0], xs[1]);
                       ⟪(A → ¬B) → (B → ¬A)⟫⟩
def A11 : Axiom := ⟨3, fun xs ↦ let (A, B, C) := (xs[0], xs[1], xs[2]);
                       ⟪((A → B) ∧ (B → C)) → (A → C)⟫⟩
def A12 : Axiom := ⟨3, fun xs ↦ let (A, B, C) := (xs[0], xs[1], xs[2]);
                       ⟪(A → B) → ((B → C) → (A → C))⟫⟩
def A13 : Axiom := ⟨3, fun xs ↦ let (A, B, C) := (xs[0], xs[1], xs[2]);
                       ⟪(A → B) → ((C → A) → (C → B))⟫⟩
def A14 : Axiom := ⟨2, fun xs ↦ let (A, B) := (xs[0], xs[1]);
                       ⟪(A → (A → B)) → (A → B)⟫⟩
def A15 : Axiom := ⟨1, fun xs ↦ let A := xs[0];
                       ⟪A → ¬A → ¬A⟫⟩
def A16 : Axiom := ⟨2, fun xs ↦ let (A, B) := (xs[0], xs[1]);
                       ⟪A → (A → B → B)⟫⟩

-- Rules
def R1 : Rule := ⟨2, fun xs ↦ let (A, B) := (xs[0], xs[1]);
                     ⟨[⟪A⟫, ⟪A → B⟫], ⟪B⟫⟩⟩
def R2 : Rule := ⟨2, fun xs ↦ let (A, B) := (xs[0], xs[1]);
                     ⟨[⟪A⟫, ⟪B⟫], ⟪A ∧ B⟫⟩⟩
def R3 : Rule := ⟨4, fun xs ↦ let (A, B, C, D) := (xs[0], xs[1], xs[2], xs[3]);
                     ⟨[⟪A → B⟫, ⟪C → D⟫], ⟪(B → C) → (A → D)⟫⟩⟩
def R4 : Rule := ⟨2, fun xs ↦ let (A, B) := (xs[0], xs[1]);
                     ⟨[⟪A → ¬B⟫], ⟪B → ¬A⟫⟩⟩
def R5 : Rule := ⟨2, fun xs ↦ let (A, B) := (xs[0], xs[1]);
                     ⟨[⟪A⟫], ⟪A → B → B⟫⟩⟩

section
variable {x y z : Variable}

-- \[TODO]: I'm not really sure how to deal with the following section...
/-
def QA1 : Axiom := ⟨1, fun xs ↦ let A := x0;
                       ⟪∀x A → A[y/x]⟫⟩
-/

end

def B : Logic := ⟨[A1, A2, A3, A4, A5, A6, A7, A8, A9], [R1, R2, R3, R4]⟩
def DJ : Logic := ⟨[A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11], [R1, R2, R3]⟩

-- Define logical consequence.

-- I'm not sure if `Set` is appropriate here.
inductive Provable (𝓵 : Logic) (Γ : Set Formula) : Formula → Prop where
  | ax {i : Fin 𝓵.axioms.length} (formulæ : Vector Formula (𝓵.axioms[i].fst)) :
      Provable 𝓵 Γ (𝓵.axioms[i].snd formulæ)
  | rule {i : Fin 𝓵.rules.length} (formulæ : Vector Formula (𝓵.rules[i].fst))
      (h : ∀ φ ∈ (𝓵.rules[i].snd formulæ).fst, Provable 𝓵 Γ φ) :
      Provable 𝓵 Γ (𝓵.rules[i].snd formulæ).snd
  | ass {γ} (h : γ ∈ Γ) : Provable 𝓵 Γ γ

notation:10 Γ " ⊢[" 𝓵 "] " φ => Provable 𝓵 Γ φ

-- ## Semantics for the Logic DJᵈQ.

structure DJModelData where
  K : Type
  p : K → Prop
  R : K → K → K → Prop
  star : K → K

abbrev DJModelData.T (djmd : DJModelData) := {x : djmd.K // djmd.p x}

def le {djmd : DJModelData} (a b : djmd.K) : Prop := ∃ x : djmd.T, djmd.R x a b
infix:60 " ≤ " => fun l r ↦ le l r

structure DJModel extends DJModelData where
  p₁ {a : K} : a ≤ a
  p₂ {a b c d} : a ≤ b → R b c d → R a c d
  p₃ {a : K} : a = star (star a)
  p₄ {a b c} : R a b c → R a (star c) (star b)
  p₅ {a b c} : R a b c → ∃ x : K, R a b x ∧ R a x c

namespace DJModel


set_option quotPrecheck false in
postfix:90 "⋆" => fun {djm : DJModelData} (a : djm.K) ↦ djm.star a

def Valuation {djm : DJModel} := { ν : djm.K → Predicate 0 → Prop //
                                       ∀ (a b : djm.K) p, a ≤ b → ν a p → ν b p}

-- Each valuation can be uniquely extended to an interpretation I on M for all propositional formulæ
def Interpretation {djm : DJModel} (ν : Valuation (djm:=djm)) (a : djm.K) (φ : Formula) : Prop :=
  match φ with
  | ⟪p()⟫   => ν.val a p
  | ⟪¬ψ⟫    => ¬Interpretation ν (a⋆) ψ
  | ⟪ψ ∧ χ⟫ => Interpretation ν a ψ ∧ Interpretation ν a χ
  | ⟪ψ ∨ χ⟫ => Interpretation ν a ψ ∨ Interpretation ν a χ
  | ⟪ψ → χ⟫ => ∀ b c : djm.K, djm.R a b c → Interpretation ν b ψ → Interpretation ν c χ
  | _       => ⊥

def DJMValid (djm : DJModel) (Γ : Set Formula) (φ : Formula) : Prop :=
    ∀ ν : Valuation (djm:=djm),
      (∀ γ ∈ Γ, ∀ t : djm.T, Interpretation ν t γ) → ∀ t : djm.T, Interpretation ν t φ

def DJValid (Γ : Set Formula) (φ : Formula) : Prop := ∀ djm : DJModel, DJMValid djm Γ φ

lemma star_le_star {djm : DJModel} {a b : djm.K} (le : a ≤ b) : b⋆ ≤ a⋆ := by
  have ⟨x, h⟩ := le
  use x
  exact djm.p₄ h

lemma hereditary_lemma {djm : DJModel} {a b : djm.K} {φ ν} (le : a ≤ b) (h : Interpretation ν a φ) :
    Interpretation ν b φ := by
  match φ with
  | ⟪p()⟫   => exact ν.property a b p le h
  | ⟪¬ψ⟫    =>
    intro H
    exact h (hereditary_lemma (star_le_star le) H)
  | ⟪ψ → χ⟫ =>
    intro c d h' h''
    exact h c d (djm.p₂ le h') h''
  | ⟪ψ ∧ χ⟫ => exact And.imp (hereditary_lemma le) (hereditary_lemma le) h
  | ⟪ψ ∨ χ⟫ => exact Or.imp (hereditary_lemma le) (hereditary_lemma le) h

lemma entailment_lemma₁ {djm : DJModel} {φ ψ ν}
    (h : ∀ a : djm.K, Interpretation ν a φ → Interpretation ν a ψ) :
    ∀ t : djm.T, Interpretation ν t ⟪φ → ψ⟫ := by
  intro t _ c _ h'
  exact h c (hereditary_lemma (by use t) h')

lemma entailment_lemma₂ {djm : DJModel} {Γ φ ψ}
    (h : ∀ ν, ∀ a : djm.K, Interpretation ν a φ → Interpretation ν a ψ) :
    DJMValid djm Γ ⟪φ → ψ⟫ := by
  intro ν h'
  exact fun t => entailment_lemma₁ (h ν) t

lemma entailment_lemma₃ {Γ φ ψ}
    (h : ∀ djm : DJModel, ∀ ν, ∀ a : djm.K, Interpretation ν a φ → Interpretation ν a ψ) :
    DJValid Γ ⟪φ → ψ⟫ := by
  intro djm
  exact entailment_lemma₂ (h djm)

notation:10 Γ " ⊨ " φ => DJValid Γ φ

theorem soundness {Γ φ} (h : Γ ⊢[DJ] φ) : Γ ⊨ φ := by
  match h with
  | .ass h' => exact fun djm ν a ↦ a φ h'
  | .ax formulæ =>
    expose_names
    match i with
    | ⟨0, _⟩ =>
      change Γ ⊨ A1.snd formulæ
      simp [A1]
      apply entailment_lemma₃
      intro djm ν a h'
      exact h'
    | ⟨1, _⟩ =>
      change Γ ⊨ A2.snd formulæ
      simp [A2]
      apply entailment_lemma₃
      intro djm ν a h'
      exact h'.1
    | ⟨2, _⟩ =>
      change Γ ⊨ A3.snd formulæ
      simp [A3]
      apply entailment_lemma₃
      intro djm ν a h'
      exact h'.2
    | ⟨3, _⟩ =>
      change Γ ⊨ A4.snd formulæ
      simp [A4]
      apply entailment_lemma₃
      intro djm ν a h' b c h'' h'''
      exact ⟨h'.left b c h'' h''', h'.right b c h'' h'''⟩
    | ⟨4, _⟩ =>
      change Γ ⊨ A5.snd formulæ
      simp [A5]
      apply entailment_lemma₃
      intro djm ν a h'
      exact Or.symm (Or.inr h')
    | ⟨5, _⟩ =>
      change Γ ⊨ A6.snd formulæ
      simp [A6]
      apply entailment_lemma₃
      intro djm ν a h'
      exact Or.symm (Or.inl h')
    | ⟨6, _⟩ =>
      change Γ ⊨ A7.snd formulæ
      simp [A7]
      apply entailment_lemma₃
      intro djm ν a h'
      intro b c h'' h'''
      cases h''' with
      | inl h''' => exact h'.1 b c h'' h'''
      | inr h''' => exact h'.2 b c h'' h'''
    | ⟨7, _⟩ =>
      change Γ ⊨ A8.snd formulæ
      simp [A8]
      apply entailment_lemma₃
      intro djm ν a h'
      exact and_or_left.mp h'
    | ⟨8, _⟩ =>
      change Γ ⊨ A9.snd formulæ
      simp [A9]
      apply entailment_lemma₃
      intro djm ν a h'
      simp [Interpretation, ← djm.p₃] at h'
      exact h'
    | ⟨9, _⟩ =>
      change Γ ⊨ A10.snd formulæ
      simp [A10]
      apply entailment_lemma₃
      intro djm ν a h' b c h''
      simp [Interpretation]
      contrapose
      simp
      intro h'''
      rw [djm.p₃ (a:= b)]
      exact h' (c⋆) (b⋆) (djm.p₄ h'') h'''
    | ⟨10, _⟩ =>
      change Γ ⊨ A11.snd formulæ
      simp [A11]
      apply entailment_lemma₃
      intro djm _ _ h' b c h'' h'''
      let ⟨x, ⟨h₁, h₂⟩⟩ := djm.p₅ h''
      exact h'.right x c h₂ (h'.left b x h₁ h''')
  | .rule formulæ h' =>
    expose_names
    match i with
    | ⟨0, _⟩ =>
      change Γ ⊨ (R1.snd formulæ).2
      simp [R1]
      sorry
      /-
      change ∀ φ ∈ (R1.snd formulæ).1, φ ∈ Γ at h'
      simp [R1] at h'
      intro djm ν h'' t
      have ⟨x, hx⟩ := djm.p₁ (a:=t)
      exact h'' _ h'.right x t t hx (h'' _ h'.left t)
      -/
    | ⟨1, _⟩ =>
      change Γ ⊨ (R2.snd formulæ).2
      simp [R2]
      sorry
      /-
      change ∀ φ ∈ (R2.snd formulæ).1, φ ∈ Γ at h'
      simp [R2] at h'
      intro djm ν h'' t
      exact ⟨h'' _ h'.left t, h'' _ h'.right t⟩
      -/
    | ⟨2, _⟩ =>
      change Γ ⊨ (R3.snd formulæ).2
      simp [R3]
      sorry
      /-
      change ∀ φ ∈ (R3.snd formulæ).1, φ ∈ Γ at h'
      simp [R3] at h'
      intro djm ν h'' t b c rtbc h'''
      apply hereditary_lemma (by use t)
      intro d e rbde h''''
      let ⟨x, hx⟩ := djm.p₁ (a:=e)
      let ⟨y, hy⟩ := djm.p₁ (a:=d)
      exact h'' _ h'.right x e e hx (h''' d e rbde (h'' _ h'.left y d d hy h''''))
      -/

end DJModel

/-
  This is a playground where I'm trying to work out some syntax for dealing with DJ Logic.

  assume h : φ  -- This creates a "hypothesis" h representing φ with some subscript set as the rank

  The following are simple, DNI DNE AI AE OI Distributivity
  →I is also simple, it simply pops off the last assumption off the stack

  from h : ((A → B) ∧ (B → C)) ∧ (D → C) derive (A ∨ D → C) by
    have h₁ : (A → B) := by h.left.left
    have h₂ : (B → C) := by h.left.right
    have h₃ : (D → C) := by h.right
    -- In here, I cannot use h₁ A to get B basically. That is the second condition.
    -- The first condition is already accounted for.
    from h' : A ∨ D derive C by
      from h'' : A derive C by
        have hB : B := h₂ h''
        exact h₂ hB
      exact h' h'' h₃
    exact h'
  exact h

  Okay, I'm not so sure about the final condition.
-/


inductive DJRestriction : Finset Nat → Finset Nat → Type
  | empty {s} : DJRestriction s ∅
  | nonempty {s s'} : (h' : s'.Nonempty) → (h : s.Nonempty) → s'.max' h' < s.max' h →
                      s \ {s.max' h} = s' ∨ s \ {s.max' h} = ∅ → DJRestriction s s'

inductive DJLevelledFormula : Nat → Formula → Finset Nat → Type
  | hyp {l} : (φ : Formula) → DJLevelledFormula l φ {l + 1}
  | ifIntro {l φ ψ s} : DJLevelledFormula l φ {l + 1} →
      DJLevelledFormula (l + 1) ψ (s ∪ {l + 1}) → (l + 1) ∉ s → DJLevelledFormula l ⟪φ → ψ⟫ s
  | ifElim {l φ ψ s s'} : DJRestriction s s' → DJLevelledFormula l φ s → DJLevelledFormula l ⟪φ → ψ⟫ s' →
      DJLevelledFormula l ψ (s ∪ s')
  | andIntro {l φ ψ s} : DJLevelledFormula l φ s → DJLevelledFormula l ψ s → DJLevelledFormula l ⟪φ ∧ ψ⟫ s
  | andElim₁ {l φ ψ s} : DJLevelledFormula l ⟪φ ∧ ψ⟫ s → DJLevelledFormula l φ s
  | andElim₂ {l φ ψ s} : DJLevelledFormula l ⟪φ ∧ ψ⟫ s → DJLevelledFormula l ψ s
  | orIntro₁ {l φ ψ s} : DJLevelledFormula l φ s → DJLevelledFormula l ⟪φ ∨ ψ⟫ s
  | orIntro₂ {l φ ψ s} : DJLevelledFormula l ψ s → DJLevelledFormula l ⟪φ ∨ ψ⟫ s
  | orElim {l φ ψ χ s s'} : DJRestriction s s' → DJLevelledFormula l ⟪φ ∨ ψ⟫ s →
                          DJLevelledFormula l ⟪φ → χ⟫ s' → DJLevelledFormula l ⟪ψ → χ⟫ s' →
                          DJLevelledFormula l χ (s ∪ s')
  | negElim {l φ ψ s s'} : DJRestriction s s' → DJLevelledFormula l ⟪¬ψ⟫ s →
                          DJLevelledFormula l ⟪φ → ψ⟫ s' → DJLevelledFormula l ⟪¬φ⟫ (s ∪ s')
  | dni {l φ s} : DJLevelledFormula l φ s → DJLevelledFormula l ⟪¬¬φ⟫ s
  | dne {l φ s} : DJLevelledFormula l ⟪¬¬φ⟫ s → DJLevelledFormula l φ s
  | distrib {l φ ψ χ s} : DJLevelledFormula l ⟪φ ∧ (ψ ∨ χ)⟫ s → DJLevelledFormula l ⟪(φ ∧ ψ) ∨ (φ ∧ χ)⟫ s
  | reit {l φ s} : (n : Nat) → DJLevelledFormula l φ s → DJLevelledFormula (l + n) φ s

def isInnerMost : DJLevelledFormula k φ s → Bool
  | .hyp _ | .ifIntro _ _ _ => false
  | .ifElim _ φ ψ | .andIntro φ ψ | .negElim _ φ ψ => isInnerMost φ && isInnerMost ψ
  | .orElim _ φ ψ χ => isInnerMost φ && isInnerMost ψ && isInnerMost χ
  | .andElim₁ φ | .andElim₂ φ | .orIntro₁ φ | .orIntro₂ φ | .dni φ | .dne φ | .distrib φ
  | .reit _ φ =>
    isInnerMost φ

/-
inductive InnerMostProof : DJLevelledFormula k φ s → Prop
  | ifElim {φ ψ h} : InnerMostProof φ (s := s) → InnerMostProof ψ (s := s') → InnerMostProof (.ifElim h φ ψ)
  | andIntro {φ ψ} : InnerMostProof φ → InnerMostProof ψ → InnerMostProof (.andIntro φ ψ)
  | andElim₁ {φ} : InnerMostProof φ → InnerMostProof (.andElim₁ φ)
  | andElim₂ {φ} : InnerMostProof φ → InnerMostProof (.andElim₂ φ)
  | orIntro₁ {φ} : InnerMostProof φ → InnerMostProof (.orIntro₁ φ)
  | orIntro₂ {φ} : InnerMostProof φ → InnerMostProof (.orIntro₂ φ)
  | orElim {h φ ψ χ} : InnerMostProof φ → InnerMostProof ψ → InnerMostProof χ →
                       InnerMostProof (.orElim h φ ψ χ)
  | negElim {h φ ψ} : InnerMostProof φ → InnerMostProof ψ → InnerMostProof (.negElim h φ ψ)
  | dni {φ} : InnerMostProof φ → InnerMostProof (.dni φ)
  | dne {φ} : InnerMostProof φ → InnerMostProof (.dne φ)
  | distrib {φ} : InnerMostProof φ → InnerMostProof (.distrib φ)
  | reit {n φ} : InnerMostProof (.reit n φ)
instance decidable_InnerMostProof : (ψ : DJLevelledFormula k φ s) → Decidable (InnerMostProof ψ)
  | .ifElim r φ ψ =>
    match decidable_InnerMostProof φ, decidable_InnerMostProof ψ with
    | isTrue pf₁, isTrue pf₂ => isTrue (.ifElim pf₁ pf₂)
    | isFalse n, _ => isFalse (fun h ↦ by sorry) --(fun h ↦ by match h with | .ifElim a b => sorry)
    | _, isFalse n => isFalse (by sorry)
  | .andIntro φ ψ =>
    match decidable_InnerMostProof φ, decidable_InnerMostProof ψ with
    | isTrue pf₁, isTrue pf₂ => isTrue (.andIntro pf₁ pf₂)
    | isFalse n, _ => isFalse (by sorry)
    | _, isFalse n => isFalse (by sorry)
  | .andElim₁ φ =>
    match decidable_InnerMostProof φ with
    | isTrue pf => isTrue (.andElim₁ pf)
    | isFalse pf => isFalse fun h ↦ by cases h; contradiction
  | .andElim₂ φ =>
    match decidable_InnerMostProof φ with
    | isTrue pf => isTrue (.andElim₂ pf)
    | isFalse pf => isFalse fun h ↦ by cases h; contradiction
  | .orIntro₁ φ =>
    match decidable_InnerMostProof φ with
    | isTrue pf => isTrue (.orIntro₁ pf)
    | isFalse pf => isFalse fun h ↦ by cases h; contradiction
  | .orIntro₂ φ =>
    match decidable_InnerMostProof φ with
    | isTrue pf => isTrue (.orIntro₂ pf)
    | isFalse pf => isFalse fun h ↦ by cases h; contradiction
  | .orElim _ φ ψ χ =>
    match decidable_InnerMostProof φ, decidable_InnerMostProof ψ, decidable_InnerMostProof χ with
    | isTrue pf₁, isTrue pf₂, isTrue pf₃ => isTrue (.orElim pf₁ pf₂ pf₃)
    | isFalse n, _, _ => isFalse (by sorry)
    | _, isFalse n, _ => isFalse (by sorry)
    | _, _, isFalse n => isFalse (by sorry)
  | .negElim _ φ ψ =>
    match decidable_InnerMostProof φ, decidable_InnerMostProof ψ with
    | isTrue pf₁, isTrue pf₂ => isTrue (.negElim pf₁ pf₂)
    | isFalse n, _ => isFalse (fun () ↦ by sorry)
    | _, isFalse n => isFalse (by sorry)
  | .dni φ =>
    match decidable_InnerMostProof φ with
    | isTrue pf => isTrue (.dni pf)
    | isFalse pf => isFalse fun h ↦ by cases h; contradiction
  | .dne φ =>
    match decidable_InnerMostProof φ with
    | isTrue pf => isTrue (.dne pf)
    | isFalse pf => isFalse fun h ↦ by cases h; contradiction
  | .distrib φ =>
    match decidable_InnerMostProof φ with
    | isTrue pf => isTrue (.distrib pf)
    | isFalse pf => isFalse fun h ↦ by cases h; contradiction
  | .reit n φ => isTrue .reit
  | _ => sorry
-/

def FDJMValid (Γ : Set Formula) (φ : Formula) : Prop :=
    (∀ γ ∈ Γ, DJLevelledFormula 0 γ ∅) → ∃ x : DJLevelledFormula 0 φ ∅, x = x

theorem soundness_DJ_fitch {Γ φ} (h : Γ ⊢[DJ] φ) : FDJMValid Γ φ := by
  match h with
  | .ax formulæ =>
    expose_names
    match i with
    | ⟨0, _⟩ =>
      change FDJMValid Γ (A1.snd formulæ)
      simp [A1]
      intro h
      let φ := formulæ[0]'(Nat.zero_lt_succ 0)
      have h := DJLevelledFormula.hyp (l := 0) φ
      use .ifIntro h (DJLevelledFormula.reit 1 h) (Finset.notMem_empty _)
    | ⟨1, _⟩ =>
      change FDJMValid Γ (A2.snd formulæ)
      simp [A2]
      intro h
      let φ := formulæ[0]'(Nat.zero_lt_succ 1)
      let ψ := formulæ[1]'(Nat.one_lt_succ_succ 0)
      have h := DJLevelledFormula.hyp (l:=0) ⟪φ ∧ ψ⟫
      use .ifIntro h (DJLevelledFormula.andElim₁ (.reit 1 h)) (Finset.notMem_empty _)
    | ⟨2, _⟩ =>
      change FDJMValid Γ (A3.snd formulæ)
      simp [A3]
      intro h
      let φ := formulæ[0]'(Nat.zero_lt_succ 1)
      let ψ := formulæ[1]'(Nat.one_lt_succ_succ 0)
      have h := DJLevelledFormula.hyp (l:=0) ⟪φ ∧ ψ⟫
      exact .ifIntro h (DJLevelledFormula.andElim₂ (.reit 1 h) ◂ by simp; exact Eq.to_iff rfl) (Finset.notMem_empty _)
    | ⟨3, _⟩ =>
      change FDJMValid Γ (A4.snd formulæ)
      simp [A4]
      intro h
      let φ := formulæ[0]'(Nat.zero_lt_succ 2)
      let ψ := formulæ[1]'(Nat.one_lt_succ_succ 1)
      let χ := formulæ[2]'(Nat.lt_add_one 2)
      have h := DJLevelledFormula.hyp (l:=0) ⟪(φ → ψ) ∧ (φ → χ)⟫
      have h' := DJLevelledFormula.hyp (l:=1) ⟪φ⟫
      have h₁ := DJLevelledFormula.ifElim (
        .nonempty (Finset.singleton_nonempty _) (Finset.singleton_nonempty _) (by simp) (by simp))
          h' (.reit 1 h.andElim₁)
      have h₂ := DJLevelledFormula.ifElim
                  (.nonempty (Finset.singleton_nonempty _) (Finset.singleton_nonempty _) (by simp)
                  (by simp)) h' (.reit 1 h.andElim₂)
      have h'' := DJLevelledFormula.andIntro h₁ h₂
      simp [Finset.union_comm] at h''
      have h''' := DJLevelledFormula.ifIntro h' (.reit 1 h'') (by simp)
      simp at h'''
      exact .ifIntro h (.reit 1 h''') (by simp)
    | ⟨4, _⟩ =>
      change FDJMValid Γ (A5.snd formulæ)
      simp [A5]
      intro h
      let φ := formulæ[0]'(Nat.zero_lt_succ 1)
      let ψ := formulæ[1]'(Nat.one_lt_succ_succ 0)
      have h := DJLevelledFormula.hyp (l:=0) φ
      exact .ifIntro h (DJLevelledFormula.orIntro₁ (.reit 1 h) ◂ by simp; exact Eq.to_iff rfl) (Finset.notMem_empty _)
    | ⟨5, _⟩ =>
      change FDJMValid Γ (A6.snd formulæ)
      simp [A6]
      intro h
      let φ := formulæ[0]'(Nat.zero_lt_succ 1)
      let ψ := formulæ[1]'(Nat.one_lt_succ_succ 0)
      have h := DJLevelledFormula.hyp (l:=0) ψ
      exact .ifIntro h (DJLevelledFormula.orIntro₂ (.reit 1 h) ◂ by simp; exact Eq.to_iff rfl) (Finset.notMem_empty _)
    | ⟨6, _⟩ =>
      change FDJMValid Γ (A7.snd formulæ)
      simp [A7]
      intro h
      let φ := formulæ[0]'(Nat.zero_lt_succ 2)
      let ψ := formulæ[1]'(Nat.one_lt_succ_succ 1)
      let χ := formulæ[2]'(Nat.lt_add_one 2)
      have h := DJLevelledFormula.hyp (l:=0) ⟪(φ → χ) ∧ (ψ → χ)⟫
      have h' := DJLevelledFormula.hyp (l:=1) ⟪φ ∨ ψ⟫
      have h'' := DJLevelledFormula.orElim (.nonempty (by simp) (by simp) (by simp) (by simp)) h' (.reit 1 h.andElim₁) (.reit 1 h.andElim₂)
      simp [Finset.union_comm] at h''
      have h''' := DJLevelledFormula.ifIntro h' (.reit 1 h'') (Finset.erase_eq_self.mp rfl)
      simp at h'''
      exact .ifIntro h (.reit 1 h''') (Finset.notMem_empty _)
    | ⟨7, _⟩ =>
      change FDJMValid Γ (A8.snd formulæ)
      simp [A8]
      intro h
      let φ := formulæ[0]'(Nat.zero_lt_succ 2)
      let ψ := formulæ[1]'(Nat.one_lt_succ_succ 1)
      let χ := formulæ[2]'(Nat.lt_add_one 2)
      have h := DJLevelledFormula.hyp (l:=0) ⟪φ ∧ (ψ ∨ χ)⟫
      exact .ifIntro h (DJLevelledFormula.distrib (.reit 1 h) ◂ by simp; exact Eq.to_iff rfl) (Finset.notMem_empty _)
    | ⟨8, _⟩ =>
      change FDJMValid Γ (A9.snd formulæ)
      simp [A9]
      intro h
      let φ := formulæ[0]'(Nat.zero_lt_succ 0)
      have h := DJLevelledFormula.hyp (l := 0) ⟪¬¬φ⟫
      exact .ifIntro h (DJLevelledFormula.dne (.reit 1 h) ◂ by simp; exact Eq.to_iff rfl) (Finset.notMem_empty _)
    | ⟨9, _⟩ =>
      change FDJMValid Γ (A10.snd formulæ)
      simp [A10]
      intro h
      let φ := formulæ[0]'(Nat.zero_lt_succ 1)
      let ψ := formulæ[1]'(Nat.one_lt_succ_succ 0)
      have h := DJLevelledFormula.hyp (l:=0) ⟪φ → ¬ψ⟫
      have h' := DJLevelledFormula.hyp (l:=1) ψ
      have h'' := DJLevelledFormula.negElim (
        .nonempty (Finset.singleton_nonempty _) (Finset.singleton_nonempty _) (by simp) (by simp))
          (.dni (.reit 1 h')) (.reit 2 h)
      simp [Finset.union_comm] at h''
      have h''' := DJLevelledFormula.ifIntro h' h'' (Finset.erase_eq_self.mp rfl)
      simp at h'''
      exact .ifIntro h (DJLevelledFormula.reit 1 h''' ◂ by simp; exact Eq.to_iff rfl) (Finset.notMem_empty _)
    | ⟨10, _⟩ =>
      change FDJMValid Γ (A11.snd formulæ)
      simp [A11]
      intro h
      let φ := formulæ[0]'(Nat.zero_lt_succ 2)
      let ψ := formulæ[1]'(Nat.one_lt_succ_succ 1)
      let χ := formulæ[2]'(Nat.lt_add_one 2)
      have h := DJLevelledFormula.hyp (l:=0) ⟪(φ → ψ) ∧ (ψ → χ)⟫
      have h₁ := h.andElim₁
      have h₂ := h.andElim₂
      have h' := DJLevelledFormula.hyp (l:=1) φ
      have h'₁ := DJLevelledFormula.ifElim (
        .nonempty (Finset.singleton_nonempty _) (Finset.singleton_nonempty _) (by simp) (by simp))
          h' (.reit 1 h₁)
      have h'₂ := DJLevelledFormula.ifElim (
        .nonempty (Finset.singleton_nonempty _) (by simp) (Nat.lt_add_one _) (
          Or.symm ((fun {α} {s} {a} => Finset.subset_singleton_iff.mp) fun ⦃a⦄ a => a)))
          h'₁ (.reit 1 h₂)
      simp [Finset.union_comm] at h'₂
      have h'' := DJLevelledFormula.ifIntro h' (.reit 1 h'₂) (by simp)
      exact .ifIntro h (.reit 1 h'') (by simp)
  | .rule formulæ h' =>
    expose_names
    match i with
    | ⟨0, _⟩ =>
      change FDJMValid Γ (R1.snd formulæ).2
      simp [R1]
      change ∀ φ ∈ (R1.snd formulæ).1, φ ∈ Γ at h'
      simp [R1] at h'
      intro h
      exact .ifElim (.empty) (h _ h'.left) (h _ h'.right)
    | ⟨1, _⟩ =>
      change FDJMValid Γ (R2.snd formulæ).2
      simp [R2]
      change ∀ φ ∈ (R2.snd formulæ).1, φ ∈ Γ at h'
      simp [R2] at h'
      intro h
      exact .andIntro (h _ h'.left) (h _ h'.right)
    | ⟨2, _⟩ =>
      change FDJMValid Γ (R3.snd formulæ).2
      simp [R3]
      change ∀ φ ∈ (R3.snd formulæ).1, φ ∈ Γ at h'
      simp [R3] at h'
      let φ := formulæ[0]'(by exact Nat.zero_lt_succ 3)
      let ψ := formulæ[1]'(by exact Nat.one_lt_succ_succ 2)
      let χ := formulæ[2]'(by (expose_names; exact Nat.lt_succ_of_lt isLt))
      let υ := formulæ[3]'(by (expose_names; exact Nat.succ_lt_succ isLt))
      intro h
      have h'' := DJLevelledFormula.hyp (l:=0) ⟪ψ → χ⟫
      have h''' := DJLevelledFormula.hyp (l:=1) ⟪φ⟫
      have h₁ := DJLevelledFormula.ifElim .empty h''' (.reit 2 (h _ h'.left))
      have h₂ := DJLevelledFormula.ifElim (.nonempty (by simp) (by simp) (by simp) (by simp)) h₁ (.reit 1 h'')
      have h₃ := DJLevelledFormula.ifElim .empty h₂ (.reit 2 (h _ h'.right))
      simp [Finset.union_comm] at h₃
      have h₄ := DJLevelledFormula.ifIntro h''' (.reit 1 h₃) (by simp)
      exact DJLevelledFormula.ifIntro h'' (.reit 1 h₄) (by simp)

-- Now, onto the completeness theorem.
/-
inductive DJQuasiProof : Formula → Finset Nat → Prop
  | thm {φ} : (h : ∅ ⊢[DJ] φ) → DJQuasiProof φ ∅
  | pref {φ ψ χ} : (DJQuasiProof ⟪φ → ψ⟫ ∅) → DJQuasiProof ⟪(χ → φ) → (χ → ψ)⟫ ∅
  | suff {φ ψ χ} : (DJQuasiProof ⟪φ → ψ⟫ ∅) → DJQuasiProof ⟪(ψ → χ) → (φ → χ)⟫ ∅
  | ifElim {φ ψ s s'} : DJRestriction s s' → DJQuasiProof φ s → DJQuasiProof ⟪φ → ψ⟫ s' →
      DJQuasiProof ψ (s ∪ s')
  | andIntro {φ ψ s} : DJQuasiProof φ s → DJQuasiProof ψ s → DJQuasiProof ⟪φ ∧ ψ⟫ s
  | andElim₁ {φ ψ s} : DJQuasiProof ⟪φ ∧ ψ⟫ s → DJQuasiProof φ s
  | andElim₂ {φ ψ s} : DJQuasiProof ⟪φ ∧ ψ⟫ s → DJQuasiProof ψ s
  | orIntro₁ {φ ψ s} : DJQuasiProof φ s → DJQuasiProof ⟪φ ∨ ψ⟫ s
  | orIntro₂ {φ ψ s} : DJQuasiProof ψ s → DJQuasiProof ⟪φ ∨ ψ⟫ s
  | orElim {φ ψ χ s s'} : DJRestriction s s' → DJQuasiProof ⟪φ ∨ ψ⟫ s →
                          DJQuasiProof ⟪φ → χ⟫ s' → DJQuasiProof ⟪ψ → χ⟫ s' →
                          DJQuasiProof χ (s ∪ s')
  | negElim {φ ψ s s'} : DJRestriction s s' → DJQuasiProof ⟪¬ψ⟫ s →
                          DJQuasiProof ⟪φ → ψ⟫ s' → DJQuasiProof ⟪¬φ⟫ (s ∪ s')
  | dni {φ s} : DJQuasiProof φ s → DJQuasiProof ⟪¬¬φ⟫ s
  | dne {φ s} : DJQuasiProof ⟪¬¬φ⟫ s → DJQuasiProof φ s
  | distrib {φ ψ χ s} : DJQuasiProof ⟪φ ∧ (ψ ∨ χ)⟫ s → DJQuasiProof ⟪(φ ∧ ψ) ∨ (φ ∧ χ)⟫ s
  | reit {φ s} : DJQuasiProof φ s → DJQuasiProof φ s
-/

inductive DJQuasiProof : Formula → Type
  | thm {φ} : (h : ∅ ⊢[DJ] φ) → DJQuasiProof φ
  | pref {φ ψ χ} : (DJQuasiProof ⟪φ → ψ⟫) → DJQuasiProof ⟪(χ → φ) → (χ → ψ)⟫
  | suff {φ ψ χ} : (DJQuasiProof ⟪φ → ψ⟫) → DJQuasiProof ⟪(ψ → χ) → (φ → χ)⟫
  | ifElim {φ ψ} : DJQuasiProof φ → DJQuasiProof ⟪φ → ψ⟫ → DJQuasiProof ψ
  | andIntro {φ ψ} : DJQuasiProof φ → DJQuasiProof ψ → DJQuasiProof ⟪φ ∧ ψ⟫
  | andElim₁ {φ ψ} : DJQuasiProof ⟪φ ∧ ψ⟫ → DJQuasiProof φ
  | andElim₂ {φ ψ} : DJQuasiProof ⟪φ ∧ ψ⟫ → DJQuasiProof ψ
  | orIntro₁ {φ ψ} : DJQuasiProof φ → DJQuasiProof ⟪φ ∨ ψ⟫
  | orIntro₂ {φ ψ} : DJQuasiProof ψ → DJQuasiProof ⟪φ ∨ ψ⟫
  | orElim {φ ψ χ} : DJQuasiProof ⟪φ ∨ ψ⟫ → DJQuasiProof ⟪φ → χ⟫ → DJQuasiProof ⟪ψ → χ⟫ → DJQuasiProof χ
  | negElim {φ ψ} :DJQuasiProof ⟪¬ψ⟫ → DJQuasiProof ⟪φ → ψ⟫ → DJQuasiProof ⟪¬φ⟫
  | dni {φ} : DJQuasiProof φ → DJQuasiProof ⟪¬¬φ⟫
  | dne {φ} : DJQuasiProof ⟪¬¬φ⟫ → DJQuasiProof φ
  | distrib {φ ψ χ} : DJQuasiProof ⟪φ ∧ (ψ ∨ χ)⟫ → DJQuasiProof ⟪(φ ∧ ψ) ∨ (φ ∧ χ)⟫
  | reit {φ} : DJQuasiProof φ → DJQuasiProof φ

theorem to_name {φ} {Γ : Set Formula} (h : ∀ γ ∈ Γ, DJQuasiProof γ) (proof : DJQuasiProof φ) :
    Γ ⊢[DJ] φ :=
  match proof with
  | .thm x => sorry -- This requires weakening, which is fine.
  | .pref ψ => sorry
  | .suff ψ => sorry
  | .ifElim ψ χ => by
    expose_names
    let formulæ : Vector Formula 2 := Vector.mk #[φ_2, φ] rfl
    refine Provable.rule (𝓵:=DJ) (i:=⟨0, Nat.zero_lt_succ [R2, R3].length⟩) (Γ:=Γ) formulæ ?_
    intro υ hυ
    cases hυ with
    | head => exact to_name h ψ
    | tail _ h' =>
      cases h' with
      | head => exact to_name h χ
      | tail => contradiction
  | .andIntro ψ χ => sorry
  | .andElim₁ ψ => sorry
  | .andElim₂ ψ => sorry
  | .orIntro₁ ψ => sorry
  | .orIntro₂ ψ => sorry
  | .orElim ψ χ υ => sorry
  | .negElim ψ χ => sorry
  | .dni ψ => sorry
  | .dne ψ => sorry
  | .distrib ψ => sorry
  | .reit ψ => sorry

-- We need to know that some things are theorems of DJ first.

lemma DJ₁ {φ ψ} : ∅ ⊢[DJ] ⟪(φ → ψ) → (φ → ¬¬ψ)⟫ := by
  sorry

lemma DJ₂ {φ} : ∅ ⊢[DJ] ⟪φ → φ⟫ := by
  sorry

lemma DJ₃ {φ ψ} : ∅ ⊢[DJ] ⟪(φ → ¬¬ψ) → (φ → ψ)⟫ := by
  sorry

lemma DJ₄ {φ ψ χ} : ∅ ⊢[DJ] ⟪(φ → ψ) ∧ (φ → χ) → (φ → (ψ ∧ χ))⟫ := by
  sorry

lemma DJ₅ {φ ψ χ} : ∅ ⊢[DJ] ⟪(φ → (ψ ∧ χ)) → (φ → ψ)⟫ := by
  sorry

lemma DJ₆ {φ ψ χ} : ∅ ⊢[DJ] ⟪(φ → (ψ ∧ χ)) → (φ → χ)⟫ := by
  sorry

lemma DJ₇ {φ ψ χ} : ∅ ⊢[DJ] ⟪(φ → ψ) → (φ → (ψ ∨ χ))⟫ := by
  sorry

lemma DJ₈ {φ ψ χ} : ∅ ⊢[DJ] ⟪(φ → χ) → (φ → (ψ ∨ χ))⟫ := by
  sorry

lemma DJ₉ {φ ψ χ υ} : ∅ ⊢[DJ] ⟪(φ → (ψ ∧ (χ ∨ υ))) → (φ → ((ψ ∧ χ) ∨ (ψ ∧ υ)))⟫ := by
  sorry

lemma DJ₁₀ {φ ψ χ} : ∅ ⊢[DJ] ⟪((φ → ψ) ∧ (ψ → χ)) → (φ → χ)⟫ := by
  sorry

lemma DJ₁₁ {φ ψ} : ∅ ⊢[DJ] ⟪(φ → ψ) → (¬ψ → ¬φ)⟫ := by
  sorry

example {A B C D : Formula} : DJLevelledFormula 0 ⟪(((A → B) ∧ (B → C)) ∧ (D → C)) → ((A ∨ D) → C)⟫ ∅ := by
  have hyp₀ : DJLevelledFormula 0 ⟪((A → B) ∧ (B → C)) ∧ (D → C)⟫ {1} := .hyp ⟪((A → B) ∧ (B → C)) ∧ (D → C)⟫
  have hyp₁ : DJLevelledFormula 1 ⟪A ∨ D⟫ {2} := .hyp ⟪A ∨ D⟫
  have hyp₂ : DJLevelledFormula 2 A {3} := .hyp A

  have : DJLevelledFormula 3 B ({3} ∪ {1}) :=
    (.ifElim (.nonempty (by simp) (by simp) (by simp) (by simp))
      (.reit 1 hyp₂)
      (.reit 3 (.andElim₁ (.andElim₁ hyp₀))))
  have lem : {3} ∪ {1} = ({1, 3} : Finset Nat) := by decide
  simp [lem] at this

  have : DJLevelledFormula 3 C _ :=
    .ifElim (.nonempty (by simp) (by simp) (Nat.lt_of_sub_eq_succ rfl) (by aesop))
      this
      (.reit 3 (.andElim₂ (.andElim₁ hyp₀)))
  simp [lem] at this

  have inner₂ : DJLevelledFormula 2 ⟪A → C⟫ {1} :=
    .ifIntro
      hyp₂
      this
      (by simp)

  have : DJLevelledFormula 2 _ _ :=
    .orElim (.nonempty (by simp) (by simp) (by simp) (by simp))
      (.reit 1 hyp₁)
      inner₂
      (.reit 2 (.andElim₂ hyp₀))
  simp [Finset.union_comm] at this

  have inner₁ : DJLevelledFormula 1 ⟪(A ∨ D) → C⟫ {1} :=
    .ifIntro
      hyp₁
      this
      (by simp)

  have inner₀ : DJLevelledFormula 0 ⟪(((A → B) ∧ (B → C)) ∧ (D → C)) → ((A ∨ D) → C)⟫ ∅ :=
    .ifIntro
      hyp₀
      inner₁
      (by simp)

  exact inner₀

/-
ifIntro
  hyp₀
  ifIntro
    hyp₁
    orElim
      reit 1 hyp₁
      ifIntro
        hyp₂
        ifElim
          ifElim
            reit 1 hyp₂
            reit 3 (andElim₁ (andElim₁ hyp₀)))
          reit 3 (andElim₂ (andElim₁ hyp₀))
      reit 2 (andElim₂ hyp₀)
-/

example {A B C D : Formula} : DJQuasiProof ⟪(((A → B) ∧ (B → C)) ∧ (D → C)) → ((A ∨ D) → C)⟫ := by

  have hyp₀ : DJQuasiProof ⟪(((A → B) ∧ (B → C)) ∧ (D → C)) → (((A → B) ∧ (B → C)) ∧ (D → C))⟫ :=
    .thm DJ₂
  have hyp₁ : DJQuasiProof ⟪(A ∨ D) → (A ∨ D)⟫ := .thm DJ₂
  have hyp₂ : DJQuasiProof ⟪A → A⟫ := .thm DJ₂

  have inner₁ : DJQuasiProof ⟪(((A → B) ∧ (B → C)) ∧ (D → C)) → ((A ∨ D) → C)⟫ :=
    sorry

  have inner₀ : DJQuasiProof ⟪(((A → B) ∧ (B → C)) ∧ (D → C)) → ((A ∨ D) → C)⟫ :=
    inner₁

  exact inner₀


-- Next, define a function that "delayers" a DJQuasiProof.

-- Using that, we can then transform precisely the inner-most proofs, using the given k and A,
-- which ensures that those details are correct.

theorem Finset.Max.idk_yet {α} [LinearOrder α] {s s' : Finset α} (h : s.Nonempty)
    (h' : (s ∪ s').max' (Nonempty.inl h) ∈ s ) : s.max' h = (s ∪ s').max' (Nonempty.inl h) := by
  have left : s.max' h ≤ (s ∪ s').max' (Nonempty.inl h) := max'_subset h subset_union_left
  have right : (s ∪ s').max' (Nonempty.inl h) ≤ s.max' h := le_max' s _ h'
  exact le_antisymm left right

theorem Finset.Max.idk_yet' {α} [LinearOrder α] {s s' : Finset α} (h : s'.Nonempty)
    (h' : (s ∪ s').max' (Nonempty.inr h) ∈ s') : s'.max' h = (s ∪ s').max' (Nonempty.inr h) := by
  have left : s'.max' h ≤ (s ∪ s').max' (Nonempty.inr h) := max'_subset h subset_union_right
  have right : (s ∪ s').max' (Nonempty.inr h) ≤ s'.max' h := le_max' s' _ h'
  exact le_antisymm left right

@[simp]
def Formula.impliesFoldOuter (φ : Formula) (transforms : List Formula) (s : Finset Nat) :
    Formula × Nat :=
  transforms.foldr (fun ψ (χ, i) ↦ (if i ∈ s then ⟪ψ → χ⟫ else χ, i.pred))
    (φ, transforms.length.pred)

-- lemma gaz : transforms.foldr (fun ψ (χ, i) ↦ (if i ∈ s then ⟪ψ → χ⟫ else χ, i.pred))

def Formula.impliesFold (φ : Formula) (transforms : List Formula) (s : Finset Nat) : Formula :=
  Prod.fst <| φ.impliesFoldOuter transforms s

lemma gaz {φ ψ : Formula} {transforms s} :
    φ.impliesFold (ψ :: transforms) s = if 0 ∈ s
      then ψ.implies <| φ.impliesFold transforms (s.image Nat.pred)
      else φ.impliesFold transforms (s.image Nat.pred) := by
  induction transforms
  case nil =>
    unfold Formula.impliesFold
    simp
  case cons χ rest ih =>
    split
    next h =>

      sorry
    next h => sorry
  -- unfold Formula.impliesFold
  -- simp
  -- split
  -- next h =>
  --   split
  --   next h' =>
  --     simp_all only [Formula.implies.injEq, true_and]
  --     sorry
  --   next h' => sorry
  -- next h => sorry

def chainPrefix {φ ψ transforms s} (proof : DJQuasiProof (φ.impliesFold transforms s))
    (f : DJQuasiProof φ → DJQuasiProof ψ) (proof₁ : ∀ χ, DJQuasiProof ⟪(χ → φ) → (χ → ψ)⟫) :
    DJQuasiProof (ψ.impliesFold transforms s) :=
  match transforms with
  | [] => by
    unfold Formula.impliesFold at *
    exact f proof
  | χ :: rest => by
    unfold Formula.impliesFold at *
    simp
    simp at proof
    split
    next h =>
      simp at h
      split at proof
      next h' =>
        -- Presumably here are two cases, one where the rest of the fold is
        -- trivial, and the other where it is not.
        sorry
      next h' => sorry -- This is impossible.
    next h =>
      split at proof
      next h' => sorry -- This is impossible.
      next h' =>
        -- have : ψ.implies (χ :: rest) s =
        let prefixed := chainPrefix
          (proof ◂ by unfold Formula.impliesFold; simp [h']) f proof₁
        sorry

def transformInner' {l φ s} (proof : DJLevelledFormula l φ s) (transforms : List Formula)
    (hl : l ≠ 0) (hl' : l.succ ≤ transforms.length)
    (h : proof ≍ DJLevelledFormula.hyp (l:=l) φ ∨ transforms.length = l.succ)
    (h' : proof ≍ DJLevelledFormula.hyp (l:=l) φ → transforms[l.pred]'(by sorry) = φ)
    : DJQuasiProof (φ.impliesFold transforms s) :=
  match h'' : proof with
  | .hyp ψ => by
    expose_names
    subst h_2
    unfold Formula.impliesFold
    simp

    sorry
  | .ifIntro ψ χ h => by
    expose_names
    have : transforms.length = l.succ := by
      sorry
    let χ' := transformInner' χ (transforms ++ [φ_1]) (by simp) (by simp; exact hl') (by aesop) (by sorry)
    unfold Formula.impliesFold at χ'
    simp [List.foldr_append, this] at χ'
    -- We need to show that `x.2 ≠ l + 1`, then we have equality.
    unfold Formula.impliesFold
    simp
    -- exact χ'
    sorry
  | .dni ψ => by
    let ψ' := transformInner' ψ transforms hl hl' (by sorry) (by sorry)
    exact chainPrefix ψ' (fun φ ↦ DJQuasiProof.dni φ) (fun χ ↦ .thm (DJ₁ (φ:=χ)))
    -- Given A → (B → (C → D)), deduce A → (B → (C → ¬¬D))
    -- Have (φ → ψ) → (φ → ¬¬ψ)
    -- Want something like (φ → ψ) → (φ → ¬¬ψ)...
    -- Maybe (φ → ψ) → (ψ → χ) → (φ → χ)
    -- A → B
    -- B → C
    -- A → C
    -- I.e., repeated prefixing!
    -- So I need to create a function which can generally perform this repeated prefixing.
    -- Then, I think, we're good to go.
  | .dne ψ =>
    -- DNE is similar to DNI
    by exact transformInner' ψ.dne transforms hl hl' h (by aesop)
  | .andElim₁ ψ => by
    -- andElims are similar
    exact transformInner' ψ.andElim₁ transforms hl hl' h (by aesop)
  | .andElim₂ ψ => by exact transformInner' ψ.andElim₂ transforms hl hl' h (by aesop)
  | _ => sorry

-- The idea is to make the return of this an unfolding thing so that it always returns the
-- items in transform as a folding thing... E.g., φ → ψ → A
def transformInner {l φ s} (proof : DJLevelledFormula l φ s) (transforms : List Formula)
    (hk : (h : l ∈ s) → l = s.max' (by use l)) (h : l ≤ transforms.length)
    (hl : l ≠ 0) :
    if l.succ ∈ s
      then DJQuasiProof (.implies (transforms.get ⟨l - 1, by sorry⟩) φ)
      else DJQuasiProof φ :=
  match proof with
  | .hyp ψ => by
    -- Now we need some Lemma or something which shows that ψ = the last element in the list.
    -- Unfortunately, l may in fact be smaller than the length of the list, if we are using hyp.
    sorry
  | .ifIntro ψ χ h => by
    expose_names
    let χ' := transformInner χ (transforms ++ [φ_1]) (by sorry) (by sorry)
    split
    next h' => contradiction

    have : l + 1 + 1 ∈ s := by sorry
    simp [this] at χ'
    -- The following holds by some strange assumption.
    -- I.e., if proof ≠ hyp ψ for any ψ, then l = transforms.length.
    have : (transforms ++ [φ_1])[l]'(by sorry) = φ_1 := by sorry
    simp [this] at χ'
    exact χ' trivial
  | .dni ψ => by
    let ψ' := transformInner ψ transforms hk h hl
    split
    next h' =>
      simp [h'] at ψ'
      exact .ifElim ψ' (.thm DJ₁)
    next h' =>
      simp [h'] at ψ'
      exact .dni ψ'
  | _ => sorry


def transformInnerSubproof {l φ s} (proof : DJLevelledFormula l φ s) (k : Nat) (A : Formula)
    (hk : (h : k ∈ s) → k = s.max' (by use k)) (hin : isInnerMost proof = true) :
    if k ∈ s then DJQuasiProof ⟪A → φ⟫ else DJQuasiProof φ :=
  match proof with
  | .hyp ψ => by contradiction
  | .ifIntro ψ χ h => by
    expose_names
    let χ' := transformInnerSubproof χ l_1 φ_1 (by sorry) (by sorry)
    simp at χ'
    let χ'' := transformInnerSubproof χ' k A (by sorry) (by sorry)

    contradiction
  | .reit n ψ => transformInnerSubproof ψ k A hk hin
  | .dni ψ => by
    let ψ' := transformInnerSubproof ψ k A hk hin
    split
    next h => exact DJQuasiProof.ifElim (cast (if_pos h) ψ') (.thm DJ₁)
    next h => exact DJQuasiProof.dni (cast (if_neg h) ψ')
  | .dne ψ => by
    let ψ' := transformInnerSubproof ψ k A hk hin
    split
    next h => exact DJQuasiProof.ifElim (cast (if_pos h) ψ') (.thm DJ₃)
    next h => exact DJQuasiProof.dne (cast (if_neg h) ψ')
  |.andIntro ψ χ => by
    let ψ' := transformInnerSubproof ψ k A hk (Bool.and_elim_left hin)
    let χ' := transformInnerSubproof χ k A hk (Bool.and_elim_right hin)
    split
    next h => exact DJQuasiProof.ifElim (.andIntro (cast (if_pos h) ψ') (cast (if_pos h) χ'))
                                        (.thm DJ₄)
    next h => exact DJQuasiProof.andIntro (cast (if_neg h) ψ') (cast (if_neg h) χ')
  | .andElim₁ ψ => by
    let ψ' := transformInnerSubproof ψ k A hk hin
    split
    next h => exact DJQuasiProof.ifElim (cast (if_pos h) ψ') (.thm DJ₅)
    next h => exact DJQuasiProof.andElim₁ (cast (if_neg h) ψ')
  | .andElim₂ ψ => by
    let ψ' := transformInnerSubproof ψ k A hk hin
    split
    next h => exact DJQuasiProof.ifElim (cast (if_pos h) ψ') (.thm DJ₆)
    next h => exact DJQuasiProof.andElim₂ (cast (if_neg h) ψ')
  | .orIntro₁ ψ => by
    let ψ' := transformInnerSubproof ψ k A hk hin
    split
    next h => exact DJQuasiProof.ifElim (cast (if_pos h) ψ') (.thm DJ₇)
    next h => exact DJQuasiProof.orIntro₁ (cast (if_neg h) ψ')
  | .orIntro₂ ψ => by
    let ψ' := transformInnerSubproof ψ k A hk hin
    split
    next h => exact DJQuasiProof.ifElim (cast (if_pos h) ψ') (.thm DJ₈)
    next h => exact DJQuasiProof.orIntro₂ (cast (if_neg h) ψ')
  | .distrib ψ => by
    let ψ' := transformInnerSubproof ψ k A hk hin
    split
    next h => exact DJQuasiProof.ifElim (cast (if_pos h) ψ') (.thm DJ₉)
    next h => exact DJQuasiProof.distrib (cast (if_neg h) ψ')
  | .ifElim h ψ χ => by
    expose_names
    have hψ : (h : k ∈ s_1) → k = s_1.max' (by use k) := by
      intro h
      have hk := hk (Finset.mem_union_left s' h)
      exact ((Finset.Max.idk_yet (by use k) (h ◂ by simp only [hk]; rfl)).symm ◂ by rw [← hk])
    have hχ : (h : k ∈ s') → k = s'.max' (by use k) := by
      intro h
      have hk := hk (Finset.mem_union_right s_1 h)
      exact ((Finset.Max.idk_yet' (by use k) (h ◂ by simp only [hk]; rfl)).symm ◂ by rw [← hk])
    let ψ' := transformInnerSubproof ψ k A hψ (Bool.and_elim_left hin)
    let χ' := transformInnerSubproof χ k A hχ (Bool.and_elim_right hin)
    split
    next =>
      split at χ'
      next h'' =>
        match _ : h with
        | .empty => simp_all
        | .nonempty h₁ h₂ h₃ h₄ =>
          exfalso
          expose_names
          rw [Eq.comm] at h_2
          subst h_2
          have hk := hk (Finset.mem_union_right s_1 h'')
          have cont : s'.max' h₁ = k :=
            Eq.symm ((fun {a b} => Nat.succ_inj.mp) (congrArg Nat.succ (hχ h'')))
          rw [cont, hk] at h₃
          exact h₃.not_ge (Finset.max'_subset h₂ (Finset.subset_union_left))
      next h'' =>
        have : k ∈ s_1 := by simp_all
        exact DJQuasiProof.ifElim (DJQuasiProof.andIntro (cast (if_pos this) ψ') χ')
                                  (DJQuasiProof.thm DJ₁₀)
    next =>
      exact DJQuasiProof.ifElim (cast (if_neg (by simp_all)) ψ') (cast (if_neg (by simp_all)) χ')
  | .negElim h ψ χ => by
    expose_names
    have hψ : (h : k ∈ s_1) → k = s_1.max' (by use k) := by
      intro h
      have hk := hk (Finset.mem_union_left s' h)
      exact ((Finset.Max.idk_yet (by use k) (h ◂ by simp only [hk]; rfl)).symm ◂ by rw [← hk])
    have hχ : (h : k ∈ s') → k = s'.max' (by use k) := by
      intro h
      have hk := hk (Finset.mem_union_right s_1 h)
      exact ((Finset.Max.idk_yet' (by use k) (h ◂ by simp only [hk]; rfl)).symm ◂ by rw [← hk])
    let ψ' := transformInnerSubproof ψ k A hψ (Bool.and_elim_left hin)
    let χ' := transformInnerSubproof χ k A hχ (Bool.and_elim_right hin)
    split
    next =>
      split at χ'
      next h'' =>
        match _ : h with
        | .empty => simp_all
        | .nonempty h₁ h₂ h₃ h₄ =>
          exfalso
          expose_names
          rw [Eq.comm] at h_2
          subst h_2
          have hk := hk (Finset.mem_union_right s_1 h'')
          have cont : s'.max' h₁ = k :=
            Eq.symm ((fun {a b} => Nat.succ_inj.mp) (congrArg Nat.succ (hχ h'')))
          rw [cont, hk] at h₃
          exact h₃.not_ge (Finset.max'_subset h₂ (Finset.subset_union_left))
      next h'' =>
        have : k ∈ s_1 := by simp_all
        exact DJQuasiProof.ifElim (DJQuasiProof.andIntro (cast (if_pos this) ψ')
                          (DJQuasiProof.ifElim χ' (DJQuasiProof.thm DJ₁₁))) (DJQuasiProof.thm DJ₁₀)
    next =>
      exact DJQuasiProof.negElim (cast (if_neg (by simp_all)) ψ') (cast (if_neg (by simp_all)) χ')
  | .orElim h ψ χ υ =>
    sorry

def transform {l s φ} (proof : DJLevelledFormula l φ s) (h : s = ∅) : DJQuasiProof φ :=
  match proof with
  | .ifIntro ψ χ h' => by
    expose_names
    if h'' : isInnerMost χ then
      exact cast (if_pos (by simp)) (transformInnerSubproof χ l_1 _ (by rw [h]; simp) h'')
    else
      sorry
  | .ifElim h' ψ χ => DJQuasiProof.ifElim (transform ψ (by simp_all)) (transform χ (by simp_all))
  | .andIntro ψ χ => DJQuasiProof.andIntro (transform ψ h) (transform χ h)
  | .andElim₁ ψ => DJQuasiProof.andElim₁ (transform ψ h)
  | .andElim₂ ψ => DJQuasiProof.andElim₂ (transform ψ h)
  | .orIntro₁ ψ => DJQuasiProof.orIntro₁ (transform ψ h)
  | .orIntro₂ ψ => DJQuasiProof.orIntro₂ (transform ψ h)
  | .orElim h' ψ χ υ =>
    DJQuasiProof.orElim (transform ψ (by simp_all)) (transform χ (by simp_all))
                        (transform υ (by simp_all))
  | .dni ψ => DJQuasiProof.dni (transform ψ h)
  | .dne ψ => DJQuasiProof.dne (transform ψ h)
  | .negElim h' ψ χ =>  DJQuasiProof.negElim (transform ψ (by simp_all)) (transform χ (by simp_all))
  | .distrib ψ => DJQuasiProof.distrib (transform ψ h)
  | .reit _ ψ => transform ψ h
  | .hyp _ => by simp_all


-- Finally, we can create some nice wrappers for doing these proofs in Lean.

/-
lemma test₁ (A B C D) : DJLevelledFormula ⟪(((A → B) ∧ (B → C)) ∧ (D → C)) → (A ∨ D → C)⟫ ∅ := by
  have h := DJLevelledFormula.hyp ⟪((A → B) ∧ (B → C)) ∧ (D → C)⟫ 0
  apply DJLevelledFormula.ifIntro ?_ h (by exact fun a => a)
  · -- have : ((∅ : Set Nat).union (Set.singleton 0)) = Set.singleton 0 := by sorry
    --simp [this]
    have h₁ := (DJLevelledFormula.andElim₁ h).andElim₁
    have h₂ := (DJLevelledFormula.andElim₁ h).andElim₂
    have h₃ := DJLevelledFormula.andElim₂ h
    have h' := DJLevelledFormula.hyp ⟪A ∨ D⟫ 1
    apply DJLevelledFormula.ifIntro ?_ h' (by sorry)
    · have h'' := DJLevelledFormula.hyp A 2
      have h''' := DJLevelledFormula.ifIntro (by sorry) h'' (by sorry)

      sorry
-/
