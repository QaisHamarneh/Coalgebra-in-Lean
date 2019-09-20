import coalgebra.Coalgebra

namespace Kripke_Structure

universes u v w

variable (Properties : Type u)             -- Elementry properties

structure Kripke (Φ : Type u): Type (max u (v+1)) :=  
                (State : Type v)
                (T : State → set State)
                (v : State → set Φ)

instance  Kripke_to_State : has_coe_to_sort (Kripke Properties):=
    ⟨Type v, λ K, K.State⟩ 

variables {K K1 K2 : Kripke.{u v} Properties}

--notation s ` ⟹ `  t := (s , t) ∈ Kripke.T

inductive φ
    | prop          : Properties → φ 
    | TRUE   {}     : φ
    | FALSE  {}     : φ
    | box   {}      : φ → φ
    | diamond {}    : φ → φ
    | and {}        : φ → φ → φ
    | or  {}        : φ → φ → φ
    | not {}        : φ → φ 



prefix ` # ` :100        := φ.prop 
prefix ` □ ` :10         := φ.box
prefix ` ◇ ` :20        := φ.diamond
prefix ` ¬ `             := φ.not
notation p1 ` ∧ ` p2     := φ.and p1 p2
notation p1 ` ∨ ` p2     := φ.or p1 p2



open φ 

def satisfy (s : K.State):
    K.State →  φ Properties  →   Prop
    | s (#p)        :=  p  ∈ K.v s
    | s TRUE        :=  true
    | s FALSE       :=  false
    | s □ phi       :=  ∀ t :K.State, t ∈ K.T s → satisfy t phi
    | s ◇ phi       :=  ∃ t :K.State, t ∈ K.T s → satisfy t phi
    | s (p1 ∧ p2)   := satisfy s p1 ∧ satisfy s p2 
    | s (p1 ∨ p2)   := satisfy s p1 ∨ satisfy s p2 
    | s ¬ phi       := ¬ satisfy s phi 

notation s ` ⊨ ` phi := satisfy s phi



def is_homomorphism {A B : Kripke Properties} (σ : A → B) : Prop :=
        (∀ a₁ a₂ :A , a₂ ∈ A.T a₁ → (σ a₂) ∈ B.T (σ a₁)) ∧ 
        (∀ (a : A) (b : B) , b ∈ B.T (σ a) →
                ∃ a': A ,  a' ∈ A.T a ∧ σ a' = b) ∧ 
        (∀ a : A , A.v a = B.v (σ a))


def is_bisimulation 
        (R : set (K1 × K2)) : Prop :=
        ∀ (s1 : K1) (s2 : K2), 
            (s1 , s2) ∈ R → 
            (
                K1.v s1 = K2.v s2 
                    ∧ 
                ∀ t1 : K1, K1.T s1 t1 → 
                    ∃ t2 :K2, K2.T s2 t2 ∧ 
                        (t1 , t2) ∈ R
                    ∧
                ∀ t2 : K2, K2.T s2 t2 → 
                    ∃ t1 :K1, K1.T s1 t1 ∧ 
                        (t1 , t2) ∈ R
            )

def is_bisimilar {K : Kripke Properties} 
        (B :set (K × K)) : Prop :=
    ∀ R : set (K × K), 
        @is_bisimulation Properties K K
        R → R ⊆ B

notation s1 ` ~ ` s2 := 
    ∃ B : set (Kripke × Kripke), 
        is_bisimilar B ∧ (s1 , s2) ∈ B






end Kripke_Structure


open Kripke_Structure
open Kripke_Structure.Kripke
open Kripke_Structure.φ

def Kr : Kripke char := 
{   
    State   := nat,
    T       := λ a b, b = a + 1,
    v       := (λ c , {'a'}) 
}

