import category_theory.category
import category_theory.functor
import category_theory.types

import tactic.tidy

import set_category.diagram_lemmas
import help_functions

namespace category_set

universes v u


open classical function set category_theory help_functions



local notation f ` ⊚ `:80 g:80 := category_struct.comp g f


abbreviation left_cancel {C : Type v} [category C]
    {A B C : C}
    (f : A ⟶ B) [mo : mono f] {g h : C ⟶ A} : 
    (f ⊚ g = f ⊚ h) → g = h := assume m, (cancel_mono f).1 m

abbreviation right_cancel {C : Type v} [category C]
    {A B C : C}
    (f : A ⟶ B) [ep: epi f] {g h : B ⟶ C} : 
    (g ⊚ f = h ⊚ f) → g = h := assume e, (cancel_epi f).1 e


variables {F : Type u ⥤ Type u} 
        {A B : Type u}
        


/--
    The next two lemmas are already shown in the category of types
    in mathlib.category_theory.types.lean
-/
@[simp , tidy] lemma surjective_then_epi 
    (f : A ⟶ B) 
    (sur : surjective f)
        : epi f := 
            ⟨ 
                have inv_id : f ∘ (surj_inv sur) = id := funext (surj_inv_eq sur) ,
                assume Z g h (w: g ∘ f = h ∘ f), 
                show g = h, from 
                calc g = g ∘ id : by simp
                    ... = g ∘ f ∘ (surj_inv sur)    : by rw [inv_id]
                    ... = (g ∘ f) ∘ (surj_inv sur)  : by simp
                    ... = h ∘ f ∘ (surj_inv sur)    : by rw [w]
                    ... = h ∘ id                    : by rw [inv_id]
                    ... = h                         : by simp
            ⟩ 

 @[simp , tidy] lemma injective_then_mono
    (f : A ⟶ B) (inj: injective f)
        : mono f := 
        ⟨ 
            assume C (g h : C ⟶ A) gh,
            have s1 : ∀ a₁ a₂ , f a₁ = f a₂ → a₁ = a₂ := inj,
            have s2 : ∀ c , f (g c) = f (h c) := 
                assume c , show (f ⊚ g) c = (f ⊚ h) c,
                from by rw [gh],
            have s3 : ∀ c , g c = h c := assume c , s1 (g c) (h c) (s2 c),
            funext s3 
        ⟩              

lemma mono_preserving_functor 
    (f : A ⟶ B) 
    (inj : injective f) 
    [inhabited A]
        : mono (F.map f) := 
{ right_cancellation :=
begin
    assume (Z:Type u) 
           (Fg Fh : Z ⟶ F.obj A) 
           (w : (F.map f) ∘ Fg = (F.map f) ∘ Fh),
    let inv : B ⟶ A := inv_fun f,
    have id_inv : inv ∘ f = id := funext (left_inverse_inv_fun inj),
    
    calc
        Fg  = (@id (F.obj A)) ∘ Fg              : rfl
        ... = (𝟙 (F.obj A)) ∘ Fg                : rfl
        ... = (F.map (𝟙 A)) ∘ Fg                : by rw functor.map_id'
        ... = (F.map (@id A)) ∘ Fg              : rfl
        ... = (F.map (inv ∘ f)) ∘ Fg            : by rw id_inv
        ... = (F.map (inv ⊚ f)) ∘ Fg           : rfl
        ... = ((F.map inv) ⊚ (F.map f)) ∘ Fg   : by rw functor.map_comp
        ... = (F.map inv) ∘ ((F.map f) ∘ Fg)    : rfl
        ... = (F.map inv) ∘ ((F.map f) ⊚ Fg)   : rfl
        ... = (F.map inv) ∘ ((F.map f) ⊚ Fh)   : by rw w
        ... = (F.map inv) ∘ ((F.map f) ∘ Fh)    : rfl
        ... = ((F.map inv) ∘ (F.map f)) ∘ Fh    : rfl
        ... = ((F.map inv) ⊚ (F.map f)) ∘ Fh   : rfl
        ... = (F.map (inv ⊚ f)) ∘ Fh           : by rw functor.map_comp
        ... = (F.map (inv ∘ f)) ∘ Fh            : rfl
        ... = (F.map (@id A)) ∘ Fh              : by rw id_inv
        ... = (F.map (𝟙 A)) ∘ Fh                : rfl
        ... = (𝟙 (F.obj A)) ∘ Fh                : by rw functor.map_id'
        ... = (@id (F.obj A)) ∘ Fh              : rfl
        ... = Fh                                : rfl
end 
}


           
end category_set




