import category_theory.types
import help_functions
import set_category.colimits.Sum
import set_category.colimits.Coequalizer

import tactic.tidy

universes u v

namespace Pushout
open category_theory 
     set 
     classical
     help_functions
     sum
     Sum
     Coequalizer


local notation f ` ⊚ `:80 g:80 := category_struct.comp g f

def is_pushout  {X : Type v} [category X]
    {A B₁ B₂: X} (f : A ⟶ B₁) (g : A ⟶ B₂)
    (P : X) (p₁ : B₁ ⟶ P) (p₂ : B₂ ⟶ P)
    : Prop
    :=  p₁ ⊚ f = p₂ ⊚ g ∧ 
        Π (Q : X) 
          (q₁ : B₁ ⟶ Q)
          (q₂ : B₂ ⟶ Q),
          q₁ ⊚ f = q₂ ⊚ g →
                (∃! h : P ⟶ Q, 
                q₁ = h ⊚ p₁ ∧ q₂ = h ⊚ p₂)


lemma coequalizer_sum_is_pushout_cat 
    {X : Type v} [category X]
    {A B₁ B₂: X} (f : A ⟶ B₁) (g : A ⟶ B₂)
    (S P : X) (s₁ : B₁ ⟶ S) (s₂ : B₂ ⟶ S)
    (p : S ⟶ P)
    (is_sm : is_sum S s₁ s₂)
    (is_coeq: is_coequalizer (s₁ ⊚ f) (s₂ ⊚ g) p):
    is_pushout f g P (p ⊚ s₁) (p ⊚ s₂)
    := 
    begin
        have comm : (p ⊚ s₁) ⊚ f = (p ⊚ s₂) ⊚ g :=
            by tidy, 
        split,
        exact comm,
        intros Q q₁ q₂ qfg,
        have sm : _ := is_sm Q q₁ q₂,
        let s := some sm,
        have spec : q₁ = s ⊚ s₁ ∧ q₂ = s ⊚ s₂
            := (some_spec sm).1,
        have sf_sg : s ⊚ s₁ ⊚ f = s ⊚ s₂ ⊚ g :=
            calc (s ⊚ s₁) ⊚ f 
                    = q₁ ⊚ f      : by rw ← spec.1
                ... = q₂ ⊚ g      : qfg
                ... = s ⊚ s₂ ⊚ g : by rw spec.2,
        have coeq : ∃! (h : P ⟶ Q), h ⊚ p = s
         := is_coeq.2 Q s (by tidy),
        
        let h := some coeq,
        have h_spec : s = h ⊚ p := eq.symm (some_spec coeq).1,

        use h,
        split,
        split,
        by simp [h_spec , spec.1],
        by simp [h_spec , spec.2],
        intros q spec_q,
        have h01 : q₁ = q ⊚ p ⊚ s₁ := by tidy,
        have h02 : q₂ = q ⊚ p ⊚ s₂ := by tidy,

        have q_s : q ⊚ p = s := 
                jointly_epi_cat s₁ s₂ is_sm (q ⊚ p) s
                    (spec.1 ▸ (eq.symm h01)) 
                    (spec.2 ▸ (eq.symm h02)),

        exact (some_spec coeq).2 q q_s
    end

variables   {A B₁ B₂: Type u} 
            (f : A ⟶ B₁)
            (g : A ⟶ B₂)


lemma coequalizer_sum_is_pushout :
    let S := B₁ ⊕ B₂ in
    let B_Θ := @theta A S (inl ∘ f) (inr ∘ g) in
    let π_Θ := @coequalizer A S (inl ∘ f) (inr ∘ g) in
    is_pushout f g B_Θ (π_Θ ∘ inl) (π_Θ ∘ inr)
    := 
    begin
        intros S B_Θ π_Θ,
        have is_sm : _ := @disjoint_union_is_sum B₁ B₂,
        have is_coeq: _ := @quot_is_coequalizer A S (inl ∘ f) (inr ∘ g),
        have comm : (π_Θ ∘ inl) ∘ f = (π_Θ ∘ inr) ∘ g :=
            by tidy, 
        split,
        exact comm,
        intros Q q₁ q₂ qfg,
        have sm : _ := is_sm Q q₁ q₂,
        let s := some sm,
        have spec : q₁ = s ∘ inl ∧ q₂ = s ∘ inr
            := (some_spec sm).1,
        have sf_sg : s ∘ inl ∘ f = s ∘ inr ∘ g :=
            calc (s ∘ inl) ∘ f 
                    = q₁ ∘ f      : by rw ← spec.1
                ... = q₂ ∘ g      : qfg
                ... = s ∘ inr ∘ g : by rw spec.2,
        have coeq : ∃! (h : B_Θ → Q), h ∘ π_Θ = s
         := is_coeq.2 Q s sf_sg,
        
        let h := some coeq,
        have h_spec : s = h ∘ π_Θ := eq.symm (some_spec coeq).1,

        use h,
        split,
        split,
        by simp [h_spec , spec.1],
        by simp [h_spec , spec.2],
        intros q spec_q,
        have q_s : q ∘ π_Θ = s := 
                jointly_epi s (q ∘ π_Θ) 
                    (spec.1 ▸ (eq.symm spec_q.1)) 
                    (spec.2 ▸ (eq.symm spec_q.2)),


        exact (some_spec coeq).2 q q_s
    end





end Pushout
