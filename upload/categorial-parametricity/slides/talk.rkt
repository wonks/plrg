#lang at-exp slideshow
(require latex-pict
         pict/conditional
         pict/flash
         pict/shadow
         ppict/2
         ppict/slideshow2
         slideshow/code
         slideshow/staged-slide
         slideshow-text-style
         threading)

(define $ (curry tex-math #:scale 3.5))
(define $$ (curry tex-display-math #:scale 4))

(define *global-font* "IBM Plex Sans")
(define *mono-font* "Julia Mono")

(current-main-font *global-font*)
(current-code-font *mono-font*)
(get-current-code-font-size (thunk 20)) ;; ???

;;;; helper functions
(define (frame p)
  (refocus (cc-superimpose
            p
            (rounded-rectangle (+ (pict-width p) 10)
                               (+ (pict-height p) 10)
                               #:border-width 3
                               #:border-color "blue"))
           p))

(define-syntax-rule (pslide/staged [name ...] arg ...)
  (staged [name ...] (pslide arg ...)))

(define (authors whos where)
  (with-text-style
    #:defaults [#:face *global-font*]
    ([author-name #:size 30 #:color "blue"]
     [institution #:size 20])

    (vc-append (current-line-sep)
               (apply hc-append 50
                      (for/list ([who (in-list whos)])
                        (colorize (author-name who) "blue")))
               (blank (/ (current-font-size) 3))
               (scale/improve-new-text (institution where) 0.8))))

(define (take* lst n)
  (if (> n (length lst))
      lst
      (take lst n)))

(define (make-bang radius [text ""])
  (define bang (cc-superimpose (colorize (filled-flash radius radius) "red")
                               (colorize (filled-flash (- radius (/ radius 5)) (- radius (/ radius 5))) "orange")))
  (with-text-style
    #:defaults [#:face *global-font*]
    ([bang-t #:size (round (/ radius 6))])
    (cc-superimpose bang (bang-t text))))

(define (section-card text)
  (pslide
   (with-text-style
     #:defaults [#:face *global-font*]
     ([t #:size 100 #:bold? #t])
     (t text))))

;;;; actual slides
(define (title-slide)
  (define reciprocating-saw
    (scale-to-fit (bitmap "coconut.jpg") (* 0.5 (get-client-w)) (get-client-h)))

  (with-text-style
    #:defaults [#:face *global-font*]
    ([heading #:size 50 #:bold? #t])

    (pslide/staged
     [not-qualified hazel]
     #:go (coord 0 0.5 'lc)
     reciprocating-saw
     #:go (coord 0.7 0.5 'cc)
     (vc-append
      (current-line-sep)
      @heading{Categories, parametricity,}
      @heading{and a folk theorem}
      (authors
       (case stage-name
         [(not-qualified) '("Someone not qualified to talk about category theory")]
         [(hazel) '("Hazel Levine")])
       "IU PL Reading Group")))))

;;;; Haskell
(define (haskell-slides)
  (with-text-style
    #:defaults [#:face *global-font*]
    ([title #:size 50 #:bold? #t]
     [titlett #:size 50 #:bold? #t #:face *mono-font*]
     [t #:size 35]
     [tt #:size 35 #:face *mono-font*]
     [ti #:size 35 #:italic? #t]
     [item #:size 35
           #:transform (λ (p) (t #:h-append hc-append #:left-pad 30 "• " p))])

    (pslide
     #:go (coord 0.05 0.05 'lt)
     @title{The @titlett{Functor} typeclass}
     #:go (coord 0.5 0.2 'ct)
     (vc-append
      (current-line-sep)
      @tt{class Functor f where
            fmap :: (a -> b) -> f a -> f b
            (<$) :: a -> f b -> f a}
      @ti{such that:}
      @tt{fmap id = id}
      @tt{fmap (f . g) = fmap f . fmap g})
     #:go (coord 0.05 0.67 'lt)
     (vl-append
      (current-line-sep)
      @item{Represents something we can map over}
      @item{Examples: @tt{List}, @tt{Maybe}, functions}
      @item{Way more general than "taking something out of a box"}))
    (pslide
     #:go (coord 0.05 0.05 'lt)
     @title{The easy example: lists}
     #:go (coord 0.5 0.2 'ct)
     (vc-append
      (current-line-sep)
      @tt{instance Functor [] where
            fmap f [] = []
            fmap f (x:xs) = f x : fmap f xs}
      @ti{so:}
      @tt{fmap (+ 1) [1, 2, 3] = [2, 3, 4]})
     #:go (coord 0.05 0.67 'lt)
     (vl-append
      (current-line-sep)
      @item{This is a Haskell functor with the given laws (no proof for now)}
      @item{I'm pretty sure everyone in this room has seen this one}))
    (pslide
     #:go (coord 0.05 0.05 'lt)
     @title{The intuition-breaker: functions}
     #:go (coord 0.5 0.2 'ct)
     (vc-append
      (current-line-sep)
      @tt{instance Functor ((->) r) where
            fmap f g = \x -> f (g x)
            @(ghost @tt{nope})}
      @ti{so:}
      @tt{fmap (+ 5) (!! 0) $ [1, 2, 3] = 6})
     #:go (coord 0.05 0.67 'lt)
     (vl-append
      (current-line-sep)
      @item{This is also a valid functor with the given laws}
      @item{@tt{fmap id g = id g} by η,
            and similarly for @tt{fmap (f . g) h = (fmap f . fmap g) h} by β}
      @item{Functors aren't about boxes, and they're definitely not burritos!}))))

;;;; Category theory
(define (category-theory-slides)
  (with-text-style
    #:defaults [#:face *global-font*]
    ([title #:size 50 #:bold? #t]
     [titleit #:size 50 #:bold? #t #:italic? #t]
     [titlett #:size 50 #:bold? #t #:face *mono-font*]
     [t #:size 35]
     [tt #:size 35 #:face *mono-font*]
     [ti #:size 35 #:italic? #t]
     [foot #:size 15]
     [cred #:size 10]
     [item #:size 35
           #:transform (λ (p) (t #:h-append hc-append #:left-pad 30 "• " p))])

    (pslide
     #:go (coord 0.05 0.05 'lt)
     @title{What's a category?}
     #:go (coord 0.05 0.20 'lt)
     (vl-append
      (current-line-sep)
      @t{A category @${\mathcal{C}} is:}
      @item{a @ti{collection} of objects, @${\mathrm{Ob}(\mathcal{C})}}
      @item{a @ti{collection} of morphisms between @${x, y : \mathrm{Ob}(\mathcal{C})}, @${\mathrm{Hom}_{\mathcal{C}}(x, y)}}
      @item{a @ti{binary operation}, @${\circ : \prod_{a, b, c : \mathrm{Ob}(\mathcal{C})} \mathrm{Hom}(a, b) \times \mathrm{Hom}(b, c) \to \mathrm{Hom} (a, c)}}
      @ti{such that:}
      @item{If @${f : a \to b, g : b \to c, h : c \to d}, @${h \circ (g \circ f) = (h \circ g) \circ f}}
      @item{For all @${x : \mathrm{Ob}(\mathcal{C})}, there is a morphism @${1_x} such that:})
     #:go (coord 0.10 0.70 'lt)
     (vl-append
      (current-line-sep)
      @item{if @${f : a \to x}, @${1_x \circ f = f}}
      @item{if @${g : x \to b}, @${g \circ 1_x = g}}))

    (pslide
     #:go (coord 0.05 0.05 'lt)
     @title{Examples of categories}
     #:go (coord 0.05 0.20 'lt)
     (vl-append
      (current-line-sep)
      @item{@${\mathbf{Set}, \mathbf{Grp}, \mathbf{Ring}, \mathbf{Top}}, @ti{basically any mathematical object}}
      @item{@${\mathbf{Hask}}, the @ti{syntactic category}* of Haskell programs}
      @item{@tt{Types}, the category in the @foot{haphazard} Agda formalization of this talk's claim}
      @item{Any partially ordered set @${P} (called a @ti{thin category}):})
     #:go (coord 0.12 0.49 'lt)
     @t{@${\mathrm{Ob}(P) = P,\ \mathrm{Hom}(x, y) = \{*\} \mathrm{\ if\ } x \leq y, \mathrm{\ else\ } \emptyset}}
     #:go (coord 0.05 0.54 'lt)
     @item{For any monoid @${M}, the category @${\mathbf{B}M}:}
     #:go (coord 0.12 0.62 'lt)
     @t{@${\mathrm{Ob}(\mathbf{B}M) = \{*\},\ \mathrm{Hom}(*, *) = M}}
     #:go (coord 0.85 0.75 'rc)
     (vc-append
      (current-line-sep)
      (scale-to-fit (bitmap "BS3.png") (* 0.3 (get-client-w)) (get-client-h))
      @cred{Source: Category Theory in Context by Emily Riehl})
     #:go (coord 0.05 0.95 'lt)
     @foot{* Yes I know about the Andrej Bauer blog post, shut up})

    (pslide
     #:go (coord 0.05 0.05 'lt)
     @title{Functors are category homomorphisms}
     #:go (coord 0.05 0.20 'lt)
     (vl-append
      (current-line-sep)
      @t{Given categories @${\mathcal{C}, \mathcal{D}}, a functor is a pair of maps @${F : \mathcal{C} \to \mathcal{D}}:}
      @item{@${F_\mathrm{Ob} : \mathrm{Ob}(\mathcal{C}) \to \mathrm{Ob}(\mathcal{D})}}
      @item{@${F_\mathrm{Hom} : \prod_{x, y : \mathrm{Ob}(\mathcal{C})} \mathrm{Hom}_\mathcal{C}(x, y) \to \mathrm{Hom}_\mathcal{D}(F_\mathrm{Ob}(x), F_\mathrm{Ob}(y))}}
      @item{We usually just write @${F} for both when it can be inferred from context}
      @ti{such that:}
      @item{For all @${x : \mathrm{Ob}(\mathcal{C})}, @${F(1_x) = 1_{F(x)}}}
      @item{For all @${f : a \to b, g : b \to c} in @${\mathcal{C}}, @${F(g \circ f) = F(g) \circ F(f)}})
     #:go (coord 0.05 0.75 'lt)
     @t{...seem familiar?}
     @t{That's because @tt{Functor} in Haskell represents functors @${\mathbf{Hask} \to \mathbf{Hask}}!})

    (pslide
     #:go (coord 0.05 0.05 'lt)
     @title{Proof: @titlett{map} is (part of) a functor}
     #:go (coord 0.05 0.20 'lt)
     @t{I'm doing this on the board!}
     @t{If you want the formalism, go look at the Agda.})

    (pslide
     #:go (coord 0.05 0.05 'lt)
     @title{Other examples of functors}
     #:go (coord 0.05 0.20 'lt)
     (vl-append
      (current-line-sep)
      @item{Any functor in Haskell is a functor @${\mathbf{Hask} \to \mathbf{Hask}}}
      @item{A functor @${\varphi : \mathbf{B}G \to \mathbf{B}H} is a group homomorphism}
      @item{A functor between thin categories (posets) is a monotone function}
      @item{From algebraic topology, the fundamental group: @${\pi_1 : \mathbf{Top} \to \mathbf{Grp}}})
     #:go (coord 0.5 0.6 'ct)
     (hc-append
      (scale-to-fit
       (bitmap "group-functor1.jpg")
       (* (get-client-w) 0.4) (get-client-h))
      (scale-to-fit
       (bitmap "group-functor2.jpg")
       (* (get-client-w) 0.4) (get-client-h)))
     @cred{Source: math3ma.com, "What is a functor? Definition and Examples, Part 1"})

    (pslide
     #:go (coord 0.05 0.05 'lt)
     @title{@titleit{Oh no}: functor homomorphisms}
     #:go (coord 0.05 0.20 'lt)
     (vl-append
      (current-line-sep)
      @t{Given categories @${\mathcal{C}, \mathcal{D}}, and two functors @${F, G : \mathcal{C} \to \mathcal{D}}...}
      @t{a natural transformation @${\eta : F \Rightarrow G} is a dependent function})
     #:go (coord 0.50 0.35 'ct)
     @$${\eta : \prod_{x : \mathrm{Ob}(\mathcal{C})} \mathrm{Hom}_\mathcal{D}(F(x), G(x))}
     #:go (coord 0.05 0.50 'lt)
     @t{such that this diagram commutes for all @${f : \mathrm{Hom}_\mathcal{C}(x, y)}:}
     #:go (coord 0.50 0.57 'ct)
     (hc-append
      50
      (scale-to-fit
       (bitmap "naturality.png")
       (/ (get-client-w) 2)
       (/ (get-client-h) 2.5))
      @t{read: @${\eta_y \circ F(f) = G(f) \circ \eta_x}}))

    (pslide
     #:go (coord 0.05 0.05 'lt)
     @title{Proof: @titlett{reverse} is natural}
     #:go (coord 0.05 0.20 'lt)
     @t{I'm doing this on the board!}
     @t{If you want the formalism, go look at the Agda.}
     #:go (coord 0.5 0.35 'ct)
     (scale-to-fit
      (bitmap "rev-naturality.png")
      (get-client-w)
      (* (get-client-h) 0.6)))))

;;;; Categorial parametricity
(define (categorial-parametricity-slides)
  (with-text-style
    #:defaults [#:face *global-font*]
    ([title #:size 50 #:bold? #t]
     [reallybig #:size 80 #:bold? #t]
     [t #:size 35]
     [tt #:size 35 #:face *mono-font*]
     [foot #:size 15]
     [cred #:size 10]
     [item #:size 35
           #:transform (λ (p) (t #:h-append hc-append #:left-pad 30 "• " p))])

    (pslide
     #:go (coord 0.05 0.05 'lt)
     @title{I think I've been here before}
     #:go (coord 0.5 0.15 'ct)
     (scale-to-fit
      (bitmap "reverse-thf.png")
      (get-client-w)
      (* (get-client-h) 0.8))
     @cred{Source: Theorems for free!, Wadler})

    (pslide
     #:go (coord 0.05 0.05 'lt)
     @title{A rephrasing of parametricity}
     #:go (coord 0.5 0.18 'ct)
     (vc-append
      @reallybig{Parametricity is a property of the}
      @reallybig{type system, that asserts that}
      @reallybig{every well-typed polymorphic}
      @reallybig{function is a}
      @reallybig{natural transformation}
      @foot{...probably.}))

    (pslide
     #:go (coord 0.05 0.05 'lt)
     @title{Natural transformations in Haskell}
     #:go (coord 0.05 0.15 'lt)
     @item{Any @tt{r :: Functor f, g => forall a. f a -> g a} is natural}
     #:go (coord 0.5 0.25 'ct)
     @tt{
       safeHead :: forall a. [a] -> Maybe a
       safeHead [] = Nothing
       safeHead (x:xs) = Just x
     }
     #:go (coord 0.5 0.45 'ct)
     (scale-to-fit
      (bitmap "safehead-natural.png")
      (get-client-w)
      (* (get-client-h) 0.55)))

    (pslide
     #:go (coord 0.05 0.05 'lt)
     @title{Getting more exact}
     #:go (coord 0.05 0.15 'lt)
     @t{What we want out of parametricity under this model is that:}
     #:go (coord 0.05 0.43 'lt)
     (vl-append
      (current-line-sep)
      @item{Types can be interpreted as functors with some corresponding @tt{fmap}}
      @item{Basic types are just constant functors}
      @item{Functions between these types are interpreted as natural transformations}
      @item{So basically, we want the category @${[\mathbf{Hask}, \mathbf{Hask}]}}))))

;;;; But not really
(define (real-categorial-parametricity-slides)
  (with-text-style
    #:defaults [#:face *global-font*]
    ([title #:size 50 #:bold? #t]
     [titleit #:size 50 #:bold? #t #:italic? #t]
     [titlett #:size 50 #:bold? #t #:face *mono-font*]
     [reallybig #:size 80 #:bold? #t]
     [t #:size 35]
     [tt #:size 35 #:face *mono-font*]
     [ti #:size 35 #:italic? #t]
     [foot #:size 15]
     [cred #:size 10]
     [item #:size 35
           #:transform (λ (p) (t #:h-append hc-append #:left-pad 30 "• " p))])

    (pslide/staged
     [diagram mapping]
     #:go (coord 0.05 0.05 'lt)
     @title{Wait, what broke?}
     #:go (coord 0.05 0.20 'lt)
     @t{Consider the function:}
     #:go (coord 0.5 0.27 'ct)
     @tt{
       weirdHead :: forall a. [a] -> (a -> a)
       weirdHead [] = \x -> x
       weirdHead (x:xs) = \_ -> x
     }
     #:go (coord 0.05 0.45 'lt)
     @t{For this to be natural, this diagram must commute:}
     #:go (coord 0.5
                 (case stage-name
                   [(diagram) 0.53]
                   [(mapping) 0.515])
                 'ct)
     (scale-to-fit
      (bitmap
       (case stage-name
         [(diagram) "weirdhead-unnatural.png"]
         [(mapping) "weirdhead-mapping.png"]))
      (get-client-w)
      (* (get-client-h)
         (case stage-name
           [(diagram) 0.45]
           [(mapping) 0.48]))))

    (pslide
     #:go (coord 0.05 0.05 'lt)
     @title{Variance issues abound}
     #:go (coord 0.05 0.20 'lt)
     (vl-append
      (current-line-sep)
      @t{Earlier, I only showed functors over @${\to} for the right argument}
      @t{What about the left?}
      @t{@${\to} is @ti{contravariant} in its first argument, but @ti{covariant} in the second})
     #:go (coord 0.05 0.45 'lt)
     (vl-append
      (current-line-sep)
      @t{This means that @${a \to k} for fixed @${k} forms a @ti{contravariant functor}:}
      @t{@${F(g \circ f) = F(f) \circ F(g)}}
      @t{(or if you like, a functor out of @${\mathcal{C}^{op}}, the @ti{dual category})})
     #:go (coord 0.05 0.75 'lt)
     (vl-append
      (current-line-sep)
      @t{But then @${\forall a. a \to a} has to be both a covariant and contravariant functor!}
      @t{So, @${a \to a} isn't a functor at all.}))

    (pslide/staged
     [normal dinatural realizable what-the-hell]
     #:go (coord 0.05 0.05 'lt)
     @title{A re-rephrasing of parametricity}
     #:go (coord 0.5 0.18 'ct)
     (vc-append
      @reallybig{Parametricity is a property of the}
      @reallybig{type system, that asserts that}
      @reallybig{every well-typed polymorphic}
      @reallybig{function is a}
      @reallybig{natural transformation})
     #:go (coord 0.12 0.85 'cc)
     (show (shadow-frame @reallybig{di-})
           (at/after dinatural))
     #:go (coord 0.5 0.5 'cc)
     (show
      (rotate
       (shadow-frame
        (vc-append
         @t{...when interpreted as realizable functors}
         @t{@${\mathbf{Per}^\mathrm{op} \times \mathbf{Per} \to \mathbf{Per}}}))
       (/ pi 8))
      (at/after realizable))
     #:go (coord 0.25 0.25 'cc)
     (show
      (rotate
       (shadow-frame
        (scale-to-fit (bitmap "excuse-me.jpg")
                      (/ (get-client-w) 5)
                      (get-client-h)))
       (- (/ pi 8)))
      (at/after what-the-hell)))

    (pslide
     #:go (coord 0.05 0.05 'lt)
     @title{...I'm scared}
     #:go (coord 0.05 0.20 'lt)
     @t{A dinatural transformation between functors @${F, G : \mathcal{C}^\mathrm{op} \times \mathcal{C} \to \mathcal{D}} is...}
     @t{uhh... this thing.}
     (scale-to-fit
      (bitmap "dinatural.png")
      (* (get-client-w) 0.9)
      (get-client-h)))

    (pslide
     #:go (coord 0.5 0.5 'cc)
     (bitmap "dinaturals-do-not-compose.png"))

    (pslide
     #:go (coord 0.05 0.05 'lt)
     @title{Further reading: actually interpreting parametricity}
     #:go (coord 0.05 0.20 'lt)
     (vl-append
      (current-line-sep)
      @item{You can use the dinatural transformation approach}
      @item{This is described in @ti{Functorial Polymorphism} by Bainbridge et al.})

     #:go (coord 0.05 0.40 'lt)
     (vl-append
      (current-line-sep)
      @item{There are other ways of doing it, namely with these objects called scones}
      @item{Again, a blog post on the topic by Mike Shulman is linked on the webpage}
      @item{At this point you've gone beyond what I'm capable of}))))

;;;; main
(module+ main
  (title-slide)
  (section-card "0. Haskell")
  (haskell-slides)
  (section-card "1. Category theory")
  (category-theory-slides)
  (section-card "2. Categorial parametricity")
  (categorial-parametricity-slides)
  (section-card "3. ...but not really")
  (real-categorial-parametricity-slides)
  (section-card "Thank you!"))
