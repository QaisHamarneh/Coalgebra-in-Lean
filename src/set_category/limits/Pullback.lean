import tactic.tidy
import set_category.diagram_lemmas
import set_category.category_set
import help_functions
import set_category.limits.Equalizer
import set_category.limits.Product
import category_theory.types





namespace Pullback

open set 
     diagram_lemmas
     classical
     function
     help_functions
     Equalizer
     Product
     category_theory
     category_set


universes v u

local notation f ` ⊚ `:80 g:80 := category_struct.comp g f


def is_pullback {X : Type v} [category X]
    {A₁ A₂ B : X}
    (f : A₁ ⟶ B) (g : A₂ ⟶ B)
    {P : X} (p₁ : P ⟶ A₁) (p₂ : P ⟶ A₂): Prop :=
    f ⊚ p₁ = g ⊚ p₂ ∧ 
    Π {Q : X} (q₁ : Q ⟶ A₁) (q₂ : Q ⟶ A₂),
        f ⊚ q₁ = g ⊚ q₂ →
            ∃! h : Q ⟶ P, q₁ = p₁ ⊚ h ∧ q₂ = p₂ ⊚ h


lemma equalizer_product_is_pullback_cat 
    {X : Type u} [category X]
    {A₁ A₂ B P E : X}
    (f : A₁ ⟶ B) (g : A₂ ⟶ B)
    (π₁ : P ⟶ A₁) (π₂ : P ⟶ A₂)
    (pr : is_product A₁ A₂ π₁ π₂)
    (e : E ⟶ P)
    (eqauliz : is_equalizer (f ⊚ π₁) (g ⊚ π₂) e) :
    is_pullback f g
        (π₁ ⊚ e)
        (π₂ ⊚ e) 
    := 
    ⟨ begin 
        tidy
     end
    ,
    begin
        intros Q q₁ q₂ fq₁_gq₂,
        let p : Q ⟶ P := some (pr  Q q₁ q₂),
        have spec_p : q₁ = π₁ ⊚ p ∧ q₂ = π₂ ⊚ p := (some_spec (pr Q q₁ q₂)).1,

        have eq_comp : f ⊚ π₁ ⊚ p  = g ⊚ π₂ ⊚ p := 
            calc f ⊚ π₁ ⊚ p   = f ⊚ (π₁ ⊚ p)   : by tidy
                    ...         = f ⊚ q₁         : by rw ← spec_p.1
                    ...         = g ⊚ q₂         : fq₁_gq₂
                    ...         = g ⊚ (π₂ ⊚ p)  : by rw spec_p.2
                    ...         = g ⊚ π₂ ⊚ p    : by tidy,

        let h : Q ⟶ E := some (eqauliz.2 p eq_comp),
        have spec_h : p = e ⊚ h := (some_spec (eqauliz.2 p eq_comp)).1,
        use h,
        have h0 : q₁ = π₁ ⊚ e ⊚ h ∧ q₂ = π₂ ⊚ e ⊚ h :=
            ⟨ 
                by simp [spec_h , spec_p.1]
                ,  
                by simp [spec_h , spec_p.2]
            ⟩ ,
        split, 
        exact h0,
        assume (y : Q ⟶ E) (spec_y : q₁ = π₁ ⊚ e ⊚ y ∧ q₂ = π₂ ⊚ e ⊚ y),
        have s0 : π₁ ⊚ (e ⊚ h) = π₁ ⊚ (e ⊚ y) := 
            calc π₁ ⊚ (e ⊚ h) = π₁ ⊚ e ⊚ h      : by tidy
                ...            = q₁                : eq.symm h0.1
                ...            = π₁ ⊚ e ⊚ y      : spec_y.1
                ...            = π₁ ⊚ (e ⊚ y)    : by tidy,
        have s1 : π₂ ⊚ (e ⊚ h) = π₂ ⊚ (e ⊚ y) := 
            calc π₂ ⊚ (e ⊚ h) = π₂ ⊚ e ⊚ h      : by tidy
            ...                = q₂                : eq.symm h0.2
            ...                = π₂ ⊚ e ⊚ y      : spec_y.2
            ...                = π₂ ⊚ (e ⊚ y)    : by tidy,
        have eh_ey : e ⊚ h = e ⊚ y := 
            jointly_mono A₁ A₂ P π₁ π₂ pr s0 s1,
        
        haveI m_e : mono e := equalizer_is_mono (f ⊚ π₁) (g ⊚ π₂) e eqauliz,
        exact left_cancel e (eq.symm eh_ey)
    end ⟩ 




variables {A₁ A₂ B : Type u}
variables (f : A₁ ⟶ B) (g : A₂ ⟶ B)

lemma equalizer_product_is_pullback :
    let P := A₁ × A₂ in 
    let π₁ : P → A₁ := λ ab, ab.1 in
    let π₂ : P → A₂ := λ ab, ab.2 in
    let E := equalizer_set (f ∘ π₁) (g ∘ π₂) in
    let e := E ↪ P in

    is_pullback f g
        (π₁ ∘ e)
        (π₂ ∘ e) 
    := 
    let P := A₁ × A₂ in 
    let π₁ : P → A₁ := λ ab, ab.1 in
    let π₂ : P → A₂ := λ ab, ab.2 in
    let E := equalizer_set (f ∘ π₁) (g ∘ π₂) in
    let e : E → P := E ↪ P in
    ⟨ begin 
        tidy
    end
    ,
    begin
        intros Q q₁ q₂ fq₁_gq₂,
        have eq := eqaulizer_set_is_equalizer (f ∘ π₁) (g ∘ π₂),
        have pr := cartesian_product_is_product A₁ A₂ Q q₁ q₂,
        let p : Q → P := some pr,
        have spec_p : q₁ = π₁ ∘ p ∧ q₂ = π₂ ∘ p := (some_spec pr).1,

        have eq_comp : f ∘ π₁ ∘ p = g ∘ π₂ ∘ p := 
            spec_p.2 ▸ (spec_p.1 ▸ fq₁_gq₂),

        let h : Q → E := some (eq.2 p eq_comp),
        have spec_h : p = e ∘ h := (some_spec (eq.2 p eq_comp)).1,
        use h,
        split, 
        have h0 : q₁ = π₁ ∘ e ∘ h ∧ q₂ = π₂ ∘ e ∘ h :=
            ⟨ 
                by simp [spec_h , spec_p.1]
                ,  
                by simp [spec_h , spec_p.2]
            ⟩ ,
        exact h0,
        assume (y : Q → E) (hy : q₁ = π₁ ∘ e ∘ y ∧ q₂ = π₂ ∘ e ∘ y),
        have s0 : π₁ ∘ e ∘ h = π₁ ∘ e ∘ y := 
                spec_h ▸ (spec_p.1 ▸ hy.1),
        have s1 : π₂ ∘ e ∘ h = π₂ ∘ e ∘ y := 
                spec_h ▸ (spec_p.2 ▸ hy.2),
        have eh_ey : e ∘ h = e ∘ y := 
            jointly_mono A₁ A₂ (A₁ × A₂) prod.fst prod.snd 
                (cartesian_product_is_product A₁ A₂) s0 s1,
        
        have elements : ∀ q, y q = h q :=
            assume q,
            have e0 : (e ∘ y) q = (e ∘ h) q := 
                by rw eh_ey,
            (inj_inclusion P E) e0,
        exact funext elements
            
    end ⟩ 







end Pullback