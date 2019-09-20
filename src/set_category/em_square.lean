
import category_theory.category
import category_theory.functor
import category_theory.types

import tactic.tidy


import set_category.diagram_lemmas
import set_category.category_set
import help_functions

namespace em_square

universes v u


open classical 
     function 
     set 
     category_theory 
     help_functions
     diagram_lemmas
     category_set



local notation f ` ⊚ `:80 g:80 := category_struct.comp g f




/--
    Given an E-M-Square
    and that a diagonal d exists that makes one triangle commute
    then so does the other triangle and d is unique
-/
lemma commutative_triangles_epi
    {C : Type v} [category C]
        {X Y Z U : C}
          (e : X ⟶ Y)
          (f : Y ⟶ U)
          (g : X ⟶ Z)
          (m : Z ⟶ U)
          (h : f ⊚ e = m ⊚ g)
          (d : Y ⟶ Z)
          [epi e] :
            (g = d ⊚ e) → 
            (∀ d₁ : Y ⟶ Z , 
                g = d₁ ⊚ e → d₁ = d)
                ∧ f = m ⊚ d
        := 
    begin
        intros g_ed,
        split,

        intros d₁ g_ed₁,
        exact eq.symm (right_cancel e (g_ed ▸ g_ed₁)), 

        have ef_edm : f ⊚ e = m ⊚ d ⊚ e := by simp [g_ed, h],
        exact right_cancel e ef_edm
    end


lemma commutative_triangles_mono 
        {C : Type v} [category C] {X Y Z U : C}
          (e : X ⟶ Y) (f : Y ⟶ U)
          (g : X ⟶ Z) (m : Z ⟶ U)
          (h : f ⊚ e = m ⊚ g) (d : Y ⟶ Z)
          [mono m] : 
    f = m ⊚ d → ((∀ d₁ : Y ⟶ Z , 
                        f = m ⊚ d₁ → d₁ = d)
                  ∧ g = d ⊚ e)
        := 
    begin 
        assume f_dm,

        split,

        assume d₁ f_dm₁,
        exact eq.symm (left_cancel m (f_dm ▸ f_dm₁)),
        
        have edm_gm : m ⊚ d ⊚ e = m ⊚ g := f_dm ▸ h,
        have edm_gm1: m ⊚ (d ⊚ e) = m ⊚ g := by tidy,
        exact eq.symm (left_cancel m edm_gm1)
    end

lemma commutative_triangles {X Y Z U : Type u}
          (e : X ⟶ Y)
          (f : Y ⟶ U)
          (g : X ⟶ Z)
          (m : Z ⟶ U)
          (h : f ⊚ e = m ⊚ g)
          (d : Y ⟶ Z) :
            ((epi e ∧ g = d ⊚ e) → 
            ((∀ d₁ : Y ⟶ Z , 
                g = d₁ ⊚ e → d₁ = d)
                ∧ f =  m ⊚ d)) ∧
            ((mono m ∧ f = m ⊚ d) → 
            ((∀ d₁ : Y ⟶ Z , 
                f =  m ⊚ d₁ → d₁ = d)
                ∧ g = d ⊚ e))
        := 
    and.intro
    (assume ⟨ep, g_ed⟩,
        begin
            have left_cancel : _ := ep.left_cancellation,
            split,

            assume d₁ g_ed₁,
            exact eq.symm (left_cancel d d₁ (g_ed ▸ g_ed₁)), 

            have ef_edm : f ⊚ e = m ⊚ d ⊚ e := by simp [g_ed, h],
            exact left_cancel f (m ⊚ d) ef_edm
        end
    )
    (assume ⟨ mo, f_dm⟩ ,
        begin 
            have right_cancel : _ := mo.right_cancellation,
            split,

            assume d₁ f_dm₁,
            exact eq.symm (right_cancel d d₁ (f_dm ▸ f_dm₁)),
            
            have edm_gm : m ⊚ d ⊚ e = m ⊚ g := 
                f_dm ▸ h,
            exact eq.symm (right_cancel (d ⊚ e) g edm_gm)
        end
    )




lemma E_M_square {X Y Z U : Type u}
          (e : X ⟶ Y) (ep : epi e)
          (f : Y ⟶ U) (g : X ⟶ Z)
          (m : Z ⟶ U) (mo : mono m)
          (h : f ⊚ e = m ⊚ g) :
          ∃! d : Y ⟶ Z , (g = d ⊚ e ∧ 
                          f = m ⊚ d) :=
begin 
    have sur : surjective e := (epi_iff_surjective e).1 ep,
    have inj : injective m  := (mono_iff_injective m).1 mo,

    have diagram_sur : _ := diagram_surjective e g sur,
    have diagram_inj : _ := diagram_injective m f inj,

    have range_e :  univ = range e :=eq.symm (iff.elim_right 
                                                range_iff_surjective sur),
    have range_f : range f = image f univ := by simp,
    have range_ef: range (f ⊚ e) = range f := 
        eq.symm (sub_range_if_surjective e f sur),

    have range_ef_gm : range (f ⊚ e) = range (m ⊚ g) :=
            eq.subst h rfl,
    have range_f_gm : range f = range (m ⊚ g) := 
            eq.subst range_ef range_ef_gm,
    have range_m_gm : range (m ⊚ g) ⊆ range m := 
        range_comp_subset_range g m,
    have range_f_m : range f ⊆ range m := 
        eq.subst (eq.symm range_f_gm) range_m_gm,

    have kern_e_g : sub_kern e g := 
        sub_kern_if_injective e f g m h inj, 

    cases (diagram_inj.2 range_f_m) with d₁ ex_uni1,
    cases (diagram_sur.2 kern_e_g)  with d₂ ex_uni2,

    have ex1 : m ∘ d₁ = f := ex_uni1.1,
    have ex2 : d₂ ∘ e = g := ex_uni2.1,

    have uni1 : ∀ d : Y ⟶ Z,  m ∘ d = f → d = d₁ := ex_uni1.2,
    have uni2 : ∀ d : Y ⟶ Z,  d ∘ e = g → d = d₂ := ex_uni2.2,

    have lemma_21_mono : _ := (commutative_triangles e f g m h d₁),
    have h1 : (∀ (d₁₁ : Y ⟶ Z), f = m ⊚ d₁₁ → d₁₁ = d₁)
                     ∧ g = d₁ ⊚ e := 
        and.right lemma_21_mono ⟨mo , eq.symm ex1⟩,
    have h2 : ∀ (d₁₁  : Y ⟶ Z), f = m ⊚ d₁₁ → d₁₁ = d₁ :=
        assume d₁₁, and.left h1 d₁₁,

    have lemma_21_epi : _ := (commutative_triangles e f g m h d₂),
    have h3 : _ := 
        and.left lemma_21_epi ⟨ep ,eq.symm ex2⟩,
    have h4 : ∀ (d₁₁  : Y ⟶ Z), g =  d₁₁ ⊚ e → d₁₁ = d₂ :=
        assume d₁₁, and.left h3 d₁₁,
    
    have d11 : g = d₁ ⊚ e := and.right h1,
    have d22 : f = m ⊚ d₂ := and.right h3,

    have d1_d2 : d₂ = d₁ := and.left h1 d₂ d22,
    have d12 : f = m ⊚ d₁ := eq.subst d1_d2 d22,

    have h5 : ∀ dₓ : Y ⟶ Z , 
            (g = dₓ ⊚ e ∧ f = m ⊚ dₓ) → dₓ = d₁ := 
            assume dₓ ged_fdm,
            uni1 dₓ (eq.symm ged_fdm.2),
    exact exists_unique.intro d₁ ⟨d11 , d12⟩ h5
end


end em_square