import set_category.diagram_lemmas
import set_category.category_set
import set_category.em_square
import help_functions

namespace coalgebra

open category_theory 
     set 
     category_set 
     diagram_lemmas 
     help_functions 
     classical
     em_square


universes v u 

local notation f ` ⊚ `:80 g:80 := category_struct.comp g f


/-- The stucture of coalgebra of signature F -/
structure Coalgebra (F : Type u ⥤ Type u) : Type (u+1) :=
    (carrier : Type u) (α : carrier ⟶ F.obj carrier)

variables {F : Type u ⥤ Type u}


/-- Allows us to use the coalgebra as a Type referring to its carrier-/
instance Coalgebra_to_sort : has_coe_to_sort (Coalgebra F) := 
    ⟨Type u,  λ 𝔸, 𝔸.carrier⟩ 

variables {𝔸 Β ℂ: Coalgebra F}
 
/--
    A Set-Category morphism(φ : A -> B) is coalgebra morphism iff
    α_B ∘ φ =  F φ ∘ α_A
-/
@[simp , tidy] def is_coalgebra_homomorphism
        (ϕ : 𝔸 →  Β) : Prop :=
        Β.α ∘ ϕ =  (F.map ϕ) ∘ 𝔸.α

/--
    The subtype of coalgebra-homomorphism
-/
def homomorphism (𝔸 Β : Coalgebra F) : set (𝔸 → Β):=
    λ ϕ , is_coalgebra_homomorphism ϕ 

 
/-- Allows us to use a homomorphism as a map-/
instance homomorphism_to_map (𝔸 Β : Coalgebra F) : 
    has_coe_to_fun (homomorphism 𝔸 Β) := 
    { F := λ _, 𝔸 → Β, coe := λ m, m.val}
    
/--
    A proof that id is a coalgebra-homomorphism
-/
lemma id_is_hom (𝔸 : Coalgebra F):
     is_coalgebra_homomorphism (@id 𝔸) := 
     show 𝔸.α ∘ id =  (F.map id) ∘ 𝔸.α, from
        calc 𝔸.α ∘ id = (𝟙 (F.obj 𝔸)) ∘ 𝔸.α     : rfl
                ...   = (F.map (𝟙 𝔸)) ∘ 𝔸.α     : by rw ← functor.map_id' F 𝔸
               
/--
    A proof that composition of two homomorphism is a coalgebra-homomorphism
-/
lemma comp_is_hom (φ : homomorphism 𝔸 Β) (ψ : homomorphism Β ℂ)
    : is_coalgebra_homomorphism (ψ ∘ φ) :=
        have ab : Β.α ∘ φ =  F.map φ ∘ 𝔸.α := φ.property,
        have bc : ℂ.α ∘ ψ =  F.map ψ ∘ Β.α := ψ.property,

        calc
        (ℂ.α ∘ ψ) ∘ φ = (F.map ψ) ∘ Β.α  ∘ φ    : by rw bc
        ... = (F.map ψ) ∘ (F.map φ) ∘ 𝔸.α      : by rw ab
        ... = ((F.map ψ) ⊚ (F.map φ)) ∘ 𝔸.α   : rfl
        ... = (F.map (ψ ⊚ φ)) ∘ 𝔸.α           : by rw ← functor.map_comp
    
 

/--
    The category of Coalgebras of the signature F (Set-F)
-/
instance coalgebra_category : category (Coalgebra F) :=
{
    hom  := λ 𝔸 Β, homomorphism 𝔸 Β,
    id   := λ 𝔸 , ⟨@id 𝔸, id_is_hom 𝔸⟩ ,
    comp := λ 𝔸 Β ℂ φ ψ, ⟨ψ ∘ φ, comp_is_hom φ ψ⟩
}


instance set_F_to_set : has_coe (𝔸 ⟶ Β) (𝔸.carrier ⟶ Β.carrier)
    := ⟨λ ϕ :𝔸 ⟶ Β, ϕ⟩ 

open function

lemma empty_hom_dom (ϕ : 𝔸.carrier ⟶ Β.carrier) 
    (em_𝔸 : ¬ nonempty 𝔸):
    is_coalgebra_homomorphism ϕ := 
    begin
        dsimp at *,
        ext1,
        have ex : ∃ a : 𝔸 , true := exists.intro x trivial,
        exact absurd (nonempty_of_exists ex) em_𝔸
    end

lemma empty_hom_codom (ϕ : 𝔸.carrier ⟶ Β.carrier) 
    (em_Β : ¬ nonempty Β):
    is_coalgebra_homomorphism ϕ := 
    begin
        dsimp at *,
        ext1,
        have ex : ∃ b : Β , true := exists.intro (ϕ x) trivial,
        exact absurd (nonempty_of_exists ex) em_Β
    end

noncomputable 
def empty_map (S : Type u) (emp : ¬ nonempty S) (X : Type u): 
    S → X := 
    graph_to_map (λ s fs, false) -- ∀ a : A , ∃! b : B, G a b
    (λ s, absurd (⟨s⟩ : nonempty S) emp)

lemma not_nonempty_empty : ¬ nonempty (∅: set 𝔸) := 
assume ⟨s⟩, by tidy

noncomputable
def empty_coalgebra : Coalgebra F :=
    {
        carrier := (∅ : set 𝔸),
        α       := empty_map (∅ : set 𝔸) not_nonempty_empty (F.obj (∅ : set 𝔸))
    } 


/--
    The inverse of homomorphism is homomorphism if the 
    the homomorphism is bijective. 
-/
theorem bij_inverse_of_hom_is_hom
    (φ : homomorphism 𝔸 Β)
    (bij : bijective φ) :  
        let inv : Β → 𝔸 := some (bijective_iff_has_inverse.1 bij) in
        is_coalgebra_homomorphism inv := 
        begin 
            intro inv,
            let hom :Β.α ∘ φ =  F.map φ ∘ 𝔸.α := φ.property,
            have has_lr_inv :left_inverse inv φ ∧ right_inverse inv φ
                := some_spec (bijective_iff_has_inverse.1 bij),

            calc 
            𝔸.α ∘ inv = id ∘ 𝔸.α ∘ inv                     : rfl
            ... = (𝟙 (F.obj 𝔸)) ∘ 𝔸.α ∘ inv                : rfl 
            ... = (F.map (𝟙 𝔸)) ∘ 𝔸.α ∘ inv                : by rw ← functor.map_id' 
            ... = (F.map id) ∘ 𝔸.α ∘ inv                   : rfl
            ... = (F.map (inv ∘ φ)) ∘ 𝔸.α ∘ inv            : by rw id_of_left_inverse has_lr_inv.1
            ... = (F.map (inv ⊚ φ)) ∘ 𝔸.α ∘ inv           : rfl
            ... = ((F.map inv) ⊚ (F.map φ)) ∘ 𝔸.α ∘ inv   : by rw ← functor.map_comp 
            ... = (F.map inv) ∘ ((F.map φ) ∘ 𝔸.α) ∘ inv    : rfl
            ... = (F.map inv) ∘ (Β.α ∘ φ) ∘ inv            : by rw hom
            ... = (F.map inv) ∘ Β.α ∘ (φ ∘ inv)            : rfl 
            ... = ((F.map inv) ∘ Β.α ∘ id)                 : by rw id_of_right_inverse has_lr_inv.2
            ... = (F.map inv) ∘ Β.α                        : rfl
        end 
/--
    Let 𝔸, Β, and ℂ be coalgebras and 
    f : A → B, g : B → C set maps, 
    so that ϕ := g ∘ f : A → C is a homomorphism.

    If f is a surjective homomorphism, then g is a homomorphism.
-/
lemma surj_to_hom  
            (f : 𝔸.carrier ⟶ Β.carrier) 
            (g : Β.carrier ⟶ ℂ.carrier) 
            (hom_gf : is_coalgebra_homomorphism (g ∘ f))
            (hom_f : is_coalgebra_homomorphism f)
            (ep : epi f) 
                : is_coalgebra_homomorphism g :=
    
        have  h1 : (ℂ.α ∘ g) ⊚ f = (F.map g ∘ Β.α) ⊚ f :=
        calc
        (ℂ.α ∘ g) ⊚ f = F.map (g ⊚ f) ∘ 𝔸.α   : hom_gf
        ... = (F.map g ⊚ F.map f) ∘ 𝔸.α        : by rw functor.map_comp
        ... = F.map g ∘ F.map f ∘ 𝔸.α           : by tidy
        ... = F.map g ∘ Β.α ∘ f                 : by rw [eq.symm hom_f],
        right_cancel f h1


/--
    If g is an injective homomorphismus, then f is a homomorphism.
-/
lemma inj_to_hom (f : 𝔸.carrier → Β.carrier) 
               (g : Β.carrier → ℂ.carrier) 
            (hom_gf : is_coalgebra_homomorphism (g ∘ f))
            (hom_g : is_coalgebra_homomorphism g)
            (inj : injective g) 
                : is_coalgebra_homomorphism f := 
    begin
        cases classical.em (nonempty Β) with n_em_Β emp_Β,
        have  h1 : (F.map g) ⊚ (F.map f) ⊚ 𝔸.α = F.map g ⊚ (Β.α ⊚ f) :=
        calc
        ((F.map g) ⊚ (F.map f)) ∘ 𝔸.α  
                = (F.map (g ⊚ f)) ∘ 𝔸.α  : by rw functor.map_comp
        ...     = F.map (g ∘ f) ∘ 𝔸.α     : rfl
        ...     = ℂ.α ∘ g ∘ f             : by rw [eq.symm hom_gf]
        ...     = (F.map g ∘ Β.α) ∘ f     : by rw [eq.symm hom_g],
        
        haveI inh_Β : inhabited Β := ⟨choice n_em_Β⟩, 

        haveI fg_mono : mono (F.map g) := mono_preserving_functor g inj,
        
        exact  left_cancel (F.map g) (eq.symm h1),

        exact empty_hom_codom f emp_Β
    end

/--
    Let ϕ : 𝔸 → Β, ψ : 𝔸 → ℂ be homomorphisms, 
    and ϕ is surjective.

    Then there exists a unique homomorphism χ : Β ⟶ ℂ, 
    such that χ ∘ ϕ = ψ 
    iff kern ϕ ⊆ kern ψ
-/
lemma coalgebra_diagram (ϕ : homomorphism 𝔸 Β) 
                        (ψ : homomorphism 𝔸 ℂ)
                        (sur : surjective ϕ)
            :   (∃! χ : homomorphism Β ℂ , χ ∘ ϕ = ψ) ↔ 
                (sub_kern ϕ ψ)
                :=
    iff.intro
    -- The "exists such χ" → "kern ϕ ⊆ kern ψ" direction:
    begin
        intro ex,
        cases ex with χ h1,

        exact h1.left ▸ (kern_comp ϕ χ) 
    end 
    -- The "kern ϕ ⊆ kern ψ" → "exists a unique χ" direction:
    begin
        intro k,
        -- using the diagram lemma of Set-Category to 
        -- prove the existance and uniqueness of such morphism 
        have ex_uni : ∃ χ : Β → ℂ, 
            (χ ∘ ϕ = ψ  ∧ ∀ χ₁, χ₁ ∘ ϕ = ψ → χ₁ = χ)
            := (diagram_surjective ϕ ψ sur).2 k,

        cases ex_uni with χ spec,
        -- χ : Β → ℂ
        -- spec : χ ∘ ϕ = ψ  ∧ ∀ χ₁, χ₁ ∘ ϕ = ψ → χ₁ = χ

        have hom_χ_ϕ : is_coalgebra_homomorphism (χ ∘ ϕ) :=
            (eq.symm spec.left) ▸ ψ.property,

        have hom_χ : is_coalgebra_homomorphism χ :=
            surj_to_hom ϕ χ hom_χ_ϕ ϕ.property 
                    ((epi_iff_surjective ϕ).2 sur),

        have unique : ∀ (χ₁ : homomorphism Β ℂ), 
                    χ₁ ∘ ϕ = ψ
                    → χ₁ = ⟨χ , hom_χ⟩ := by tidy,

        exact exists_unique.intro ⟨χ , hom_χ⟩ 
                                  spec.left unique
    end


/--
Let Q be a nonempty set,
    ϕ : 𝔸 ⟶ Β be a homomorphisms, 
    f : A → Q and g : Q → B be maps with ϕ = g ∘ f and
    f surjective and g injective

    Then there exists a unique α_Q : Q → F(Q) coalgebra structure
    such that both f and g are homomorphisms.
-/
theorem Factorization {Q : Type u}
    (ϕ : homomorphism 𝔸 Β) 
    (f : 𝔸.carrier ⟶ Q)
    (g : Q ⟶ Β.carrier)
    (h : ϕ.val = g ∘ f)
    (ep : epi f)
    (inj : injective g):
        ∃! α_Q : Q ⟶ F.obj Q , 
            @is_coalgebra_homomorphism F 𝔸 ⟨Q , α_Q⟩ f ∧ 
            @is_coalgebra_homomorphism F ⟨Q , α_Q⟩ Β g
    := 
begin
    cases classical.em (nonempty 𝔸) with n_em_𝔸 emp_𝔸,
    haveI inh_𝔸 : inhabited 𝔸 := ⟨choice n_em_𝔸⟩ ,
    haveI inh_ℚ : inhabited Q := ⟨f (default 𝔸)⟩, 
    let hom_ϕ := ϕ.property,
    /-
        Using the E-M-Square 
        A      ⟶(f)⟶     Q   ⟶(Β.α ∘ g)⟶ F(B), 
        A ⟶(F f ∘ α_𝔸)⟶ F(Q)   ⟶(F g)⟶   F(B)
    -/
    /-
        showing that the triangles commute
    -/ 

    have commute
        : (Β.α ∘ g) ∘ f = (F.map g) ∘ ((F.map f) ∘ 𝔸.α) := 
        calc Β.α ∘ g ∘ f = Β.α ∘ ϕ.val                      : by simp [h]
                 ...     = (F.map ϕ.val) ∘ 𝔸.α             : hom_ϕ
                 ...     = (F.map (g ∘ f)) ∘ 𝔸.α           : by rw [h]
                 ...     = (F.map (g ⊚ f)) ∘ 𝔸.α           : rfl
                 ...     = ((F.map g) ⊚ (F.map f)) ∘ 𝔸.α   : by rw functor.map_comp
                 ...     = (F.map g) ∘ (F.map f) ∘ 𝔸.α     : by simp,

    /-
        we get the existance and the uniqueness of d 
        the diagonal of the square and the coalgebra structure
    -/
    have em_square : _ := E_M_square
                f ep
                (Β.α ∘ g) ((F.map f) ∘ 𝔸.α) (F.map g) 
                (mono_preserving_functor g inj) 
                commute,

    cases em_square with d spec,

    have uni_d : _ := spec.2,

    let ℚ : Coalgebra F := ⟨Q , d⟩,
    
    have homomorphism_f : @is_coalgebra_homomorphism F 𝔸 ℚ f := 
        eq.symm spec.left.left,

    have homomorphism_g : @is_coalgebra_homomorphism F ℚ Β g := 
        spec.left.right,

    have unique : ∀ (α_Q : Q ⟶ F.obj Q), 
        @is_coalgebra_homomorphism F 𝔸 ⟨Q , α_Q⟩ f ∧ 
        @is_coalgebra_homomorphism F ⟨Q , α_Q⟩ Β g → 
        α_Q = d := 
        assume α_Q ⟨hom_f , hom_g⟩, 
        uni_d α_Q ⟨eq.symm hom_f , hom_g⟩,

    exact
    exists_unique.intro
        d 
        ⟨homomorphism_f , homomorphism_g⟩
        unique,

    have A_Q : nonempty Q → nonempty 𝔸 :=
       λ n_Q, ⟨some ((epi_iff_surjective f).1 ep (choice n_Q))⟩, 
    have em_Q : nonempty Q → false := 
        λ n_Q, emp_𝔸 (A_Q n_Q),
    have n_Q : ¬ (nonempty Q) := em_Q,
    let α_Q : Q → F.obj Q := empty_map Q n_Q (F.obj Q),
    have hom_f : @is_coalgebra_homomorphism F 𝔸 ⟨Q , α_Q⟩ f
        := empty_hom_dom f emp_𝔸,
    exact exists_unique.intro α_Q 
        ⟨hom_f , by tidy⟩ (by tidy)    

end


theorem factorization {Q : Type u}
    (ϕ : homomorphism 𝔸 Β) 
    (f : 𝔸.carrier ⟶ Q) (g : Q ⟶ Β.carrier)
    (h : ϕ.val = g ∘ f)
    (sur : surjective f)
    (inj : injective g) :
        (∃! α_Q : Q ⟶ F.obj Q , 
            @is_coalgebra_homomorphism F 𝔸 ⟨Q , α_Q⟩ f)
    := 
begin
    cases classical.em (nonempty 𝔸) with n_em_𝔸 emp_𝔸,
    haveI inh : inhabited 𝔸 := ⟨choice n_em_𝔸⟩ ,
    let hom_ϕ := ϕ.property,
    /-
        Using the E-M-Square 
        A      ⟶(f)⟶     Q   ⟶(Β.α ∘ g)⟶ F(B), 
        A ⟶(F f ∘ α_𝔸)⟶ F(Q)   ⟶(F g)⟶   F(B)
    -/
    /-
        showing that the triangles commute
    -/ 
    have commute
        : (Β.α ∘ g) ∘ f = (F.map g) ∘ ((F.map f) ∘ 𝔸.α) := 
        calc Β.α ∘ g ∘ f = Β.α ∘ ϕ.val                      : by simp [h]
                 ...     = (F.map ϕ.val) ∘ 𝔸.α             : hom_ϕ
                 ...     = (F.map (g ∘ f)) ∘ 𝔸.α           : by rw [h]
                 ...     = (F.map (g ⊚ f)) ∘ 𝔸.α           : rfl
                 ...     = ((F.map g) ⊚ (F.map f)) ∘ 𝔸.α   : by rw functor.map_comp
                 ...     = (F.map g) ∘ (F.map f) ∘ 𝔸.α     : by simp,
    
    haveI inh_Q : inhabited Q := ⟨f (default 𝔸)⟩ ,

    haveI epi_f : epi f := (epi_iff_surjective f).2 sur,
    haveI mono_Fg : mono (F.map g) := mono_preserving_functor g inj,
    /-
        we get the existance and the uniqueness of d 
        the diagonal of the square and the coalgebra structure
    -/
    have em_square : _ := E_M_square
        f epi_f (Β.α ∘ g) ((F.map f) ∘ 𝔸.α) 
            (F.map g) mono_Fg commute,

    cases em_square with d spec,
    
    have homomorphism_f : d ⊚ f = (F.map f) ⊚ 𝔸.α := 
        eq.symm spec.left.left,

    have com_tri_epi := commutative_triangles_epi 
        f (Β.α ∘ g) ((F.map f) ∘ 𝔸.α) (F.map g) commute d (eq.symm homomorphism_f),
    
    have uni_f : ∀ (α_Q : Q ⟶ F.obj Q), 
        @is_coalgebra_homomorphism F 𝔸 ⟨Q , α_Q⟩ f → 
        α_Q = d := 
        assume α_Q hom_f, 
        have com : α_Q ⊚ f = F.map f ∘ 𝔸.α := hom_f,
        com_tri_epi.1 α_Q (eq.symm com),

    exact exists_unique.intro d 
        homomorphism_f uni_f,

    have A_Q : nonempty Q → nonempty 𝔸 :=
       λ n_Q, ⟨some (sur (choice n_Q))⟩, 
    have em_Q : nonempty Q → false := 
        λ n_Q, emp_𝔸 (A_Q n_Q),
    have n_Q : ¬ (nonempty Q) := em_Q,
    let α_Q : Q → F.obj Q := empty_map Q n_Q (F.obj Q),
    have hom_f : @is_coalgebra_homomorphism F 𝔸 ⟨Q , α_Q⟩ f
        := empty_hom_dom f emp_𝔸,
    exact exists_unique.intro α_Q hom_f (by tidy)
end

theorem factorization_hom {Q : Type u}
    (ϕ : homomorphism 𝔸 Β) 
    (f : 𝔸.carrier ⟶ Q) (g : Q ⟶ Β.carrier)
    (h : ϕ.val = g ∘ f)
    (sur : surjective f)
    (inj : injective g)
    [inhabited 𝔸] :
    let α_Q := some (factorization ϕ f g h sur inj) in
        @is_coalgebra_homomorphism F ⟨Q , α_Q⟩ Β g := 
    begin 
        intros α_Q,
        
        have hom_ϕ := ϕ.property,
        
        have commute : (Β.α ∘ g) ∘ f = (F.map g) ∘ ((F.map f) ∘ 𝔸.α) := 
            calc Β.α ∘ g ∘ f 
                        = Β.α ∘ ϕ.val                      : by simp [h]
                    ... = (F.map ϕ.val) ∘ 𝔸.α             : hom_ϕ
                    ... = (F.map (g ∘ f)) ∘ 𝔸.α           : by rw [h]
                    ... = (F.map (g ⊚ f)) ∘ 𝔸.α           : rfl
                    ... = ((F.map g) ⊚ (F.map f)) ∘ 𝔸.α   : by rw functor.map_comp
                    ... = (F.map g) ∘ (F.map f) ∘ 𝔸.α     : by simp,
        haveI inh_Q : inhabited Q := ⟨f (default 𝔸)⟩ ,
        haveI epi_f : epi f := (epi_iff_surjective f).2 sur,
        haveI mono_Fg : mono (F.map g) := mono_preserving_functor g inj,

        have spec := some_spec (factorization ϕ f g h sur inj),

        have com_tri_epi : _ := commutative_triangles_epi 
            f (Β.α ∘ g) ((F.map f) ∘ 𝔸.α) (F.map g) commute α_Q (eq.symm spec.1),
        exact com_tri_epi.2
    end



















end coalgebra