#lang racket

;; same-as.rkt provides the same-as* helper macro that will
;; help us pretty-print same-as charts like in the book "The
;; Little Learner". How this works is not part of the talk.
(require "same-as.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; PLRG Presentation: Implementing Reverse Mode Automatic Differentiation in Racket.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; In this talk we will go through how the ∇ function from
;; the book "The Little Learner" is implemented. Most of the
;; information in this talk can be found in Appendix A of
;; the book. These notes have been adopted from the summer
;; course that Yafei Yang and I taught together with the
;; help of Professor Dan Friedman.

;; ∇ accepts as arguments a function f and the parameters
;; for f which we call θ. The result of invoking ∇ will be
;; the gradient (partial derivative) of f with respect to θ.

;; Here is the definition of ∇. Let's keep this in mind for
;; now and we will see how to define each of the functions
;; it uses.
#;
(define ∇
  (lambda (f θ)
    (let ((wrt (map* dual* θ)))
      (∇-once (f wrt) wrt))))

;; We know that gradients are rates of change of the result
;; of a function with respect to the arguments of the
;; function.

;; Say we have a function f that accepts one scalar
;; (same as Racket's number type) argument and returns a scalar,
;; let's invoke it on a scalar like this
;;   (f a)

;; To understand what the gradient of f is, we begin with
;; the expression below. We invoke f on an argument just a
;; little different from a, adjusted by a value Δa that can
;; be made arbitrarily small.
;;   (f (+ a Δa))
;;
;; We expect the result to change by a certain amount as
;; well. We refer to the amount it has changed using
;;   Δfₐ
;; Here, the subscript represents the argument(s) on which
;; f is invoked.

;; The gradient of f with respect to a is the rate of
;; change in the results of (f a) with respect to the
;; change in a. This makes it the ratio
;;    Δfₐ
;;   ————
;;    Δa
;; which should be equivalent to
;;    (- (f (+ a Δa)) (f a))
;;   ————————————————————————
;;               Δa

;; This ratio can be extended to functions of more than one
;; argument such that each argument is treated
;; independently. Let's say g takes two scalar arguments and
;; returns a scalar, and we invoke it on s and t.

;; We find the rates of change with respect to s and t
;; independently like this
;;
;;    Δg_s
;;   ——————
;;     Δs
;;
;; and
;;
;;    Δg_t
;;   ——————
;;     Δt
;;
;; where Δg_s is the change in
;;   (g s t)
;; when s is changed by Δs, and Δg_t is the change in
;;   (g s t)
;; when t is change by Δt.
;;
;; Then we put the two gradients together in a list
;;          Δg_s  Δg_t
;;   (list ————— —————)
;;           Δs    Δt

;; Any function that accepts vectors and returns a scalar
;; (such as a loss function) is treated in the same way as
;; a multi-argument function.

;; Each scalar s within the argument vectors is adjusted by
;; Δs, and the change in the result scalar is observed.
;;
;; Instead of packing the gradients into a list as we did
;; for g, we define the gradient to be a vector of the same
;; shape as the argument, but with the gradient values
;; substituting the scalars in that argument.

;; For example, let h be a function that accepts a nested
;; vector of shape
    (list 2 3)
;; i.e. there are two vector elements of the outer vector
;; constructor and 3 scalar elements for each inner vector
;; constructor. We then invoke it on this vector
#;
(vector
  (vector s1 s2 s3)
  (vector t1 t2 t3))

;; Then we find the gradient of
;;   h
;; with respect to
;;   s1, s2, s3, t1, t2 snd t3
;; and replace the scalars in the argument
#;
(vector
           Δh_s1   Δh_s2   Δh_s3
  (vector ——————  ——————  ——————)
            Δs1     Δs2     Δs3
           Δh_t1   Δh_t2   Δh_t3
  (vector ——————— ——————— ———————)
            Δt1     Δt2     Δt3
)

;; A function that accepts lists (of vectors, or of nested
;; lists) is treated similarly, so that the gradient with
;; respect to the list argument is a list with the same
;; structure, but with scalar gradients in the place where
;; the list argument has scalars.

;; In other words, for a function that produces a scalar,
;; its gradient with respect to a list or vector argument
;; has the same structure as that argument, but any scalar
;; in the argument is substituted by the corresponding
;; gradient with respect to that scalar.

;; For primitives like addition and multiplication, we
;; don't have to calculate a ratio, we can use a formula
;; instead.

;; For example, the function +
    +
;; if we change s (t) by Δs (Δt), we have the following
;; gradients
(let ((s 0.4)
      (t 0.6)
      (Δs 0.0001)
      (Δt 0.0001))
  (same-as*
    (list (/ (- (+ (+ s Δs) t) (+ s t))
             Δs)
          (/ (- (+ s (+ t Δt)) (+ s t))
             Δt))
    (list (/ (+ (+ (+ s Δs) t) (- (+ s t)))
             Δs)
          (/ (+ (+ s (+ t Δt)) (- (+ s t)))
             Δt))
    (list (/ (+ (+ (+ s Δs) t) (+ (- s) (- t)))
             Δs)
          (/ (+ (+ s (+ t Δt)) (+ (- s) (- t)))
             Δt))
    (list (/ (+ (+ (+ s (- s)) Δs) (+ t (- t)))
             Δs)
          (/ (+ (+ s (- s)) (+ (+ t (- t)) Δt))
             Δt))
    (list (/ (+ (+ 0.0 Δs) 0.0)
             Δs)
          (/ (+ 0.0 (+ 0.0 Δt))
             Δt))
    (list (/ (+ Δs 0.0) Δs)
          (/ (+ 0.0 Δt) Δt))
    (list (/ Δs Δs)
          (/ Δt Δt))
    (list 1.0 1.0)))

;; The gradients are 1.0 and 1.0 regardless of what s and t
;; are.

;; We determine the formulas similarly (the others are much
;; more complex than this) for all of the primitives we
;; use, so that each gradient is determined by a simple
;; formula based on the arguments to the primitive.

;; For example, the gradient of * with respect to two
;; scalars s and t is
#;
(list t s)

;; This means we never need to explicitly find the ratios
;; of the change in results to the change in
;; arguments. With these formulas for gradients of
;; primitives, we use a fixed rule to find the gradients of
;; functions that are built from primitives.

;; When the result of the invocation of one function, say
;; g, is an argument to another function, say f, then the
;; result of f is said to arise from the
;;   composition
;; of f and g.

;; For example, if both f and g take one scalar argument,
(define compose
  (lambda (f g)
    (lambda (s)
      (f (g s)))))

;; Then for any scalar s, the following two invocations
;; give us the same result:
(let ((f (lambda (x) (+ 5 x)))
      (g (lambda (x) (* 2 x)))
      (s 1.2))
  (same-as*
    ((compose f g) s)

    (((lambda (f g)
        (lambda (s)
          (f (g s))))
      f g)
     s)

    ((lambda (s)
       (f (g s)))
     s)

    (f (g s))))

;; We write this
;;   (f (g s))
;; in a more explicit way
#;
(let ((t (g s)))
  (f t))

;; If s itself is generated from the application of another
;; function, say h, to another scalar, say 3.72, we can
;; then unroll this invocation of h and add it to our
;; let-expression.
#;
(let ((s (h 3.72)))
  (let ((t (g s)))
    (f t)))

;; This let-expression is equivalent to
;;   (f (g (h 3.72)))
;; Here, we say that f, g and h form a
;;   chain of invocations
;; where the invocation of h is the
;;   innermost
;; and the invocation of f is the
;;   outermost

;; We can repeat this process of unrolling the component
;; functions all the way until the only functions in the
;; chain are primitive functions.

;; The scalar provides as an argument (here, 3.72) to the
;; innermost function is referred to as
;;   the argument to the chain
;; And the value produced by the outermost function of the
;; chain is referred to as
;;   the result of the chain

;; The simplest possible composition of two primitives f
;; and g can be written with this let-expression, where the
;; scalar s is a constant
#;
(let ((t (g s)))
  (f t))

;; To find the gradient of the composition of f and g,
;; let's adjust s by Δs.

;; The result of (g s) changes by Δg_s. Since (g s) is the
;; scalar t, let us give Δg_s another name Δt. The result
;; of the whole expression now changes by Δf_t. The
;; gradient of the expression with respect to s is the
;; ratio:
;;
;;    Δf_t
;;   ——————
;;     Δs
;;
;; which is the same as
;;
;;    Δf_t      Δt
;;   —————— × —————
;;     Δt       Δs
;;
;; which is the same as
;;
;;    Δf_t     Δg_s
;;   —————— × ——————
;;     Δt       Δs
;;
;; This implies that we can compute the gradient by
;;   (gradient of f w.r.t. its argument)
;;                    ×
;;   (gradient of g w.r.t. its argument)
;; where w.r.t. is short for "with respect to".

;; This is known as the chain rule. With this rule, we can
;; compute the gradient of a composition of functions using
;; the individual gradient of each of the component
;; functions. Say we have
;;   (f0 (f1 ... (fn a)))
;; Then we can compute the gradient w.r.t. a by
;;
;;   (gradient of f0 w.r.t. its argument)
;;                     ×
;;   (gradient of f1 w.r.t. its argument)
;;                     ×
;;                    ...
;;                     ×
;;   (gradient of fn w.r.t. its argument)

;; Since we are using ×, we refer to the accumulator for
;; accumulating the gradient as
;;   multiplicative accumulator
;; whose start value is 1.0. Its final value is the
;; gradient of the result of the chain w.r.t. the argument
;; of the chain.

;; If a function takes more than one argument, we
;; individually accumulate gradients with respect to each
;; scalar argument. Since there are now many scalars with
;; respect to which we find gradients, there are also as
;; many different multiplicative accumulators with each
;; participating only in the chain associated with its
;; scalar.

;; Because multiplication is associative, there are two ways
;; to walk this chain. For example, if we have a chain
;;   (f (g (h s)))
;; The gradient of this composition with respect to a can be
;; found in two ways.

;; we start with the multiplicative accumulator at 1.0,
;; then we can either:
;;   multiply it with the gradient of h w.r.t. its argument
;; then
;;   multiply it with the gradient of g w.r.t. its argument
;; then
;;   multiply it with the gradient of f w.r.t. its argument

;; or we can
;;   multiply it with the gradient of f w.r.t. its argument
;; then
;;   multiply it with the gradient of g w.r.t. its argument
;; then
;;   multiply it with the gradient of h w.r.t. its argument

;; The first way, starting at h and going
;; to f, is known as
;;   forward mode
;; automatic differentiation.

;; In this mode, we start with a multiplicative accumulator
;; with the value of 1.0. We then take the innermost
;; primitive in the chain, and multiply its gradient with
;; the initial multiplicative accumulator and continue to
;; process the chain from right to left, carrying the
;; result of the primitive itself, as well as the
;; multiplicative accumulator.

;; In forward mode, we don’t need to explicitly construct
;; chains. Gradients are found as we determine the results
;; of the primitives.

;; The problem arises when there are many scalars in a
;; function's arguments.
(define a-fun
  (lambda (x)
    (+ (* x x)
       (/ x (* 12 x)))))

;; Since a-fun is composed of many binary functions, for
;; every scalar argument of each primitive binary function,
;; we need to have a multiplicative accumulator for
;; it. This means, we have one x, but we need to have many
;; accumulators for the same argument.

;; The second way, the alternative to forward mode, is
;;   reverse mode
;; automatic differentiation. Here, we walk our chains from
;; left to right, i.e., from the outermost primitive
;; invocation all the way down to the innermost one. This
;; makes us explicitly construct a chain of primitives. We
;; construct this chain while we’re computing the result
;; scalar, but start walking the chain only when we
;; actually require the gradient.

;; Reverse mode automatic differentiation has the benefit
;; that there is no disproportionate increase in the number
;; of multiplicative accumulators for functions that
;; produce a scalar from compound arguments.

;; This allows us to maintain a fixed number of
;; multiplicative accumulators, one for each scalar in the
;; argument to the chain, and update those as we walk the
;; chains.

;; Our automatic differentiation happens at run time. We do
;; not attempt to translate functions into their equivalent
;; differentiated forms. Instead, we evaluate the result of
;; a function for given arguments, and then determine the
;; gradient of that result with respect to those arguments.

;; This means that numerical primitives, such as addition
;; and multiplication, not only determine their numerical
;; results, they also organize the chain so that gradients
;; can be determined whenever asked for.

;; In order to do this, we need a way to represent scalars
;; that consist of two parts. The first, its
;;   real
;; part, known as its r, is the numerical value of the
;; scalar. The second, its
;;   link
;; known as its k, is a function that manages the chain
;; that produced this scalar and is invoked for walking the
;; chain. We refer to this representation as
;;   a dual

;; Dual representation is inspired by dual numbers which
;; were introduced by the mathematician William Clifford in
;; 1873. Clifford's dual numbers can be considered to be
;; computing the gradient in forward mode, whereas our dual
;; representation of scalars will help us compute gradients
;; in reverse mode. You can find out more about Clifford's
;; dual numbers here:
;; https://en.wikipedia.org/wiki/Dual_number

;; Each dual is represented by a vector. While lists in
;; racket are linked lists, racket vectors are analogous to
;; contiguous arrays you see in C programs. The function
;; dual builds a vector of 3 elements. The 0th element is a
;; tag that is used to distinguish duals from other vectors,
;; the 1st element is the r, and the 2nd element is the k
(define dual
  (lambda (r k)
    (vector dual r k)))

;; To provide a unique tag, we use the function dual itself
;; as its tag. From now onwards, the variable name d and
;; variable names beginning with d all stand for duals.

;; Then we define a function dual? to check if its argument
;; is a dual.

;; We use eq? to check if two things are at the same memory
;; location. Because dual is a defined function, every time
;; we invoke it to get a dual, the first element in the
;; dual must be the same function at the same memory
;; location. That's why we can use eq?.
(define dual?
  (lambda (d)
    (cond
      ((vector? d) (eq? (vector-ref d 0) dual))
      (else #f))))

;; Here's eq? telling us that its two arguments evaluate to
;; functions that are at the same memory location.
(let ((i (lambda (x) x)))
  (eq? i (i i)))

;; Here's eq? telling us that even though both of its
;; arguments are the same lambda, they aren't equal because
;; they are not bound to the same name/memory location.
(eq? (lambda (x) x)
     (lambda (x) x))

;; For reverse mode automatic differentiation purposes, the
;; literal constants need to be duals. For this reason, we
;; treat all real numbers and duals as scalars

;; But in the Malt package, the tag and the link of a dual
;; are hidden when it is printed out. That's why we can
;; only see a real number, and sometimes when we invoke a
;; function that only works on real numbers, we get a weird
;; error message that says something like
;;   "10 is not a number".
(define scalar?
  (lambda (d)
    (cond
      ((number? d) #t)
      (else (dual? d)))))

;; Next we define functions to extract the real part and
;; the link part of a dual.
(define ρ
  (lambda (d)
    (cond
      ((dual? d) (vector-ref d 1))
      (else d))))

;; If the scalar is not a dual, there is no chain that
;; produced it. In that case the link should be a function
;; that ends the chain. We refer to this as the
;; end-of-chain function and we’ll define it shortly.
(define κ
  (lambda (d)
    (cond
      ((dual? d) (vector-ref d 2))
      (else end-of-chain))))

;; We will discuss about end-of-chain later, but we will
;; define it here for now so that the code below doesn't
;; error out.
(define end-of-chain
  (lambda (d z σ)
    (let ((g (hash-ref σ d 0.0)))
      (hash-set σ d (+ z g)))))

;; To get the gradient of the result of a function
;; w.r.t. its arguments, we now consider
;;   differentiable functions
;; such as the objective functions in machine learning.

;; For each scalar in its output, a differentiable function
;; should generate a gradient w.r.t. to all of its
;; arguments, and those gradients should have the same
;; shape as those arguments, such as our θ. But here, we
;; don’t require this generality. So, we make a
;; simplifying optimization. We produce, directly, a single
;; θ-shaped gradient that is the sum of all the individual
;; θ-shaped gradients, without actually producing those
;; individual θ-shaped gradients. This makes it easier for
;; use to follow our gradients when we use the gradient
;; descent algorithm.

;; Corresponding to differentiable functions, we have
;;   differentiables
;; Differentiables are defined as
;;   scalars
;;   lists of differentiables
;; or
;;   vectors of differentiables

;; We can think of differentiables as tree-shaped
;; (directed-acyclic-graph) structures that have scalars at
;; their leaves. The nodes in this structure are lists and
;; vectors. Further, the scalars at the leaves carry the
;; chains that produced them. When we compute the gradient
;; of a function, those scalars have to be duals, so that
;; they can carry the chain by which they are produced. By
;; using the information from the chain, we can use reverse
;; mode to compute the gradient.

;; Since differentiables are tree-shaped structures, we
;; need to have a way to traverse them can get the
;; information from the tree leaves. We have map* to do
;; this.
(define map*
  (lambda (f y)
    (cond
      ((scalar? y) (f y))
      ((list? y)
       (map (lambda (lm)
              (map* f lm))
         y))
      ((vector? y)
       (vector-map (lambda (ve)
                     (map* f ve))
         y)))))

;; This function recursively traverses the structure of
;; y. In the base test, where y is a scalar, we invoke f on
;; y, thus producing its new scalar. For lists (vectors),
;; we traverse the individual members (elements)
;; recursively.

;; Here are some examples of invoking map*.
;; Here, we pass a real number (not a dual displayed as a
;; real number!) and get another real number.
(same-as*
  (map* add1 1.0)
  (add1 1.0)
  2.0)

;; In this example, we get a vector of singletons.
(same-as*
  (map* list (vector 1.0 2.0 3.0))
  (vector-map (lambda (ve)
                (map* list ve))
    (vector 1.0 2.0 3.0))
  (vector (list 1.0) (list 2.0) (list 3.0)))

;; The dual* converts a scalar to a dual whose link part is
;; always end-of-chain. We name the duals that have
;; end-of-chain as the link
;;   truncated dual
(define dual*
  (lambda (d)
    (dual (ρ d)
      end-of-chain)))

;; Here is an example of how to use dual* with map*. We can
;; see that the second argument to map* is just like our θs.
(same-as*
  (map* dual* (list (vector 1.2 0.2) 2.2))
  (map (lambda (lm)
         (map* dual* lm))
    (list (vector 1.2 0.2) 2.2))
  (list
    (map* dual* (vector 1.2 0.2))
    (map* dual* 2.2))
  (list
    (vector-map (lambda (ve)
                  (map* dual* ve))
      (vector 1.2 0.2))
    (map* dual* 2.2))
  (list
    (vector (dual* 1.2) (dual* 0.2))
    (dual* 2.2))
  (list
    (vector (dual 1.2 end-of-chain) (dual 0.2 end-of-chain))
    (dual 2.2 end-of-chain)))
;; The above result produces a differentiable that contains
;; only truncated duals at its leaves. We refer to this kind
;; of differentiable as a truncated differentiable

;; With these definitions, we can define ∇ now
(define ∇
  (lambda (f θ)
    (let ((wrt (map* dual* θ)))
      (∇-once (f wrt) wrt))))

;; The argument f is the function for which the gradient is
;; being sought, and θ is the argument to f with respect
;; to which we’re seeking the gradient.

;; Since θ is a usually a list of tensors and since tensors
;; are either scalars or possibly nested vectors, θ is
;; itself a differentiable.

;; In ∇, we first convert our θ to a truncated
;; differentiable. This abandons any prior links that the
;; scalars in θ might contain. The effect of this is that
;; it restricts the gradient to be determined exclusively
;; on what f performs, and not on the history of θ prior to
;; the invocation of f on it. We will shortly see how
;; differentaible functions like f work.

;; This truncated differentiable is named wrt to remind us
;; that this is the θ argument to f
;;   with respect to
;; which we are determining gradients. It is worth
;; re-emphasizing that wrt is identical in structure to θ,
;; but each scalar from θ in wrt now has become a
;; truncated dual. Thus, it is also worth pointing out that
;; unlike θ, wrt always contains truncated duals at leaf
;; positions.

;; We are now ready to invoke f on its argument, wrt, which
;; is really a dressed-down θ. The truncated duals at the
;; leaves of wrt become the arguments to chains that get
;; constructed in the invocation of f. In other words, all
;; the gradients of the result of this invocation are
;; determined with respect to these truncated duals in wrt.

;; We invoke the function f on wrt. Assuming that this
;; invocation terminates, it produces a differentiable and
;; we then determine gradients for this differentiable with
;; respect to wrt. The differentiable produced is not a
;; truncated differentiable i.e, the duals at its leaf nodes
;; have links that represent the chains of primitives that
;; resulted in the computation of the dual produced after
;; invoking f. The actual determination of the gradient
;; through the links in the output of f is carried out by
;; the function ∇-once, which we now describe. Before that,
;; the fact that the result of (map* dual* θ) is bound to
;; wrt and the same wrt is used to invoke both f and ∇-once
;; plays an important role in the computation of gradients.

;; When we are walking down chains of primitives, we need a
;; structure that keeps track of gradients. Moreover, this
;; structure needs to remember one gradient for each scalar
;; in the argument.

;; We use
;;   gradient state
;; to do this.

;; A gradient state associates each scalar d in wrt with an
;; accumulator that represents the current gradient of the
;; result of the chain with respect to d. It represents the
;; sum of all the gradients of every scalar in the result
;; with respect to d.

;; We use hash tables to represent gradient states.
(define ∇-once
  (lambda (y wrt)
    (let ((σ (∇-σ y (hasheq))))
      (map* (lambda (d)
              (hash-ref σ d 0.0))
        wrt))))

;; Here, we determine a gradient state σ by invoking ∇-σ on
;; y and an empty gradient state, created with (hasheq). Now
;; σ contains the gradients of y with respect to each scalar
;; in wrt i.e., σ maps duals in wrt to the corresponding
;; gradients computed with respect to that scalar. The map*
;; function then descends in wrt and replaces every dual
;; with its corresponding gradient by looking it up in the
;; gradient store σ using the function hash-ref. hash-ref
;; searches for a dual stored in σ that is equal to d and if
;; it finds such a dual then it returns the gradient that
;; the dual maps to. If hash-ref can't find a dual in σ that
;; is equal to d then it returns its third argument which is
;; 0.0. Since hasheq was used to construct the gradient
;; store, the function eq? is used by hash-ref when checking
;; for equality of duals. The map* invocation is the reason
;; why the gradient result preserves the shape of θ.

;; Here is how ∇-σ updates the gradient state σ from the
;; differentiable y.
(define ∇-σ
  (lambda (y σ)
    (cond
      ((scalar? y)
       (let ((k (κ y)))
         (k y 1.0 σ)))
      ((list? y)
       (∇-σ-list y σ))
      ((vector? y)
       (∇-σ-vec y (sub1 (vector-length y)) σ)))))

;; Here, we traverse the structure of the differentiable y
;; recursively and accumulate gradients in σ.
;;
;; For lists, we accumulate the gradients from each member
;; by recursively invoking ∇-σ as we traverse the list,
;; using the support function ∇-σ-list.
;;
;; For vectors, we accumulate the gradients from each
;; element by recursively invoking ∇-σ as we traverse the
;; vector, using the support function ∇-σ-vec.

;; For the base test, where y is a scalar, we determine the
;; link k of the scalar y
;;   (κ y)
;; This is a function with three arguments. The first is
;; the scalar whose chain we are interested in walking. We
;; pass the scalar y itself.
;;
;; The second argument is the starting value of the
;; multiplicative accumulator as we begin walking down the
;; chain. Since we just start walking down the chain of y,
;; we provide 1.0, the initial multiplicative accumulator.
;;
;; The third argument is the gradient state we will be
;; updating with gradients. This invocation returns a
;; gradient state containing the gradients that are
;; obtained from walking the chain.

;; Here is the definition of ∇-σ-list and ∇-σ-vec. Since
;; they recursively invoke the function ∇-σ, these are
;; mutually recursive functions.
(define ∇-σ-list
  (lambda (y σ)
    (cond
      ((null? y) σ)
      (else
       (let ((σ-hat (∇-σ (list-ref y 0) σ)))
         (∇-σ-list (drop y 1) σ-hat))))))

(define ∇-σ-vec
  (lambda (y i σ)
    (let ((σ-hat (∇-σ (vector-ref y 0) σ)))
      (cond
        ((zero? i) σ-hat)
        (else (∇-σ-vec y (sub1 i) σ-hat))))))

;; Next we turn to links. Links are functions that help in
;; the walking of chains of a scalar. Let’s start with the
;; simplest case, when a scalar has the end-of-chain link
;; for real numbers and truncated duals.

;; The link end-of-chain is always invoked at the end of
;; the chain. By the time we finish walking down the chain,
;; we have the gradient associated with this chain in the
;; multiplicative accumulator, which we always refer to as
;; z.

;; The end of the chain is associated with a scalar, d,
;; which is the argument to the chain. So, our task at the
;; end of the chain is to remember the gradient z for the
;; scalar d in the gradient state σ.
#;
(define end-of-chain
  (lambda (d z σ)
    (let ((g (hash-ref σ d 0.0)))
      (hash-set σ d (+ z g)))))
;; hash-set helps us to remember the new gradient of d by
;; updating σ such that d now maps to its updated gradient
;; (+ z g). If z is the gradient result of the current
;; chain, then g is the gradient result of walking multiple
;; chains for various occurrences of d in the differential
;; function f and adding them together. The main reasons why
;; in ∇-once hash-ref can find the duals in wrt that match
;; with duals that have been hash-set in end-of chain are
;; because
;;    the d in end-of-chain and the d in ∇-once are both
;;    scalars at the leaf nodes of the differentiable wrt
;;    which is let bound in the body of ∇
;; and
;;    hash-set and hash-ref both use eq? for comparing duals
;;    stored in σ so equality of duals depends on the memory
;;    location at which they are defined at

;; In general, a single scalar d from wrt might actually
;; appear at the end of multiple chains that contribute to
;; a single result, y. This can happen, for example, when
;; the argument to a function is used more than once.

;; In that case, each occurrence of d at the end of a chain
;; makes its own contribution to the gradient of y with
;; respect to d. The final gradient here is the sum of all
;; these contributions.

;; For example, if a function f is defined as below.
#;
(define f
  (lambda (x)
    (+ x x)))

;; The result of
;;   (f d)
;; is
;;   2 × d

;; Because x is used twice in the body of f, this counts as
;; two occurrences of d.

;; The gradient of the result of + w.r.t its arguments is
;; always 1.0

;; Thus, the gradient of the addition w.r.t. to d is
(same-as*
  (+ 1.0 1.0)
  2)

#;(∇ f 3)

;; This requirement is incorporated within end-of-chain. We
;; first look up the current gradient g for d in σ using
;; hash-ref, with a default of 0.0 if d is not present in
;; σ.

;; We then add the multiplicative accumulator z to the
;; current gradient g, and remember this sum as the
;; gradient for d using hash-set.

;; Let’s look at the link of a primitive operation. The
;; addition of two scalars, +-0-0, is defined like this. It
;; accepts two scalar arguments and returns a dual where
;; the real part is the sum of the real parts of its two
;; arguments.

;; Since +-0-0 is primitive, its gradients with respect to
;; the arguments da and db are determined by a formula.
(define +-0-0-v1
  (lambda (da db)
    (dual (+ (ρ da) (ρ db))
      (lambda (d z σ)
        (let ((σ-hat ((κ da) da (* 1.0 z) σ)))
          ((κ db) db (* 1.0 z) σ-hat))))))

;; Let's see our example of f.
(define f
  (lambda (x)
    (+-0-0-v1 x x)))

(∇ f 3.2)

;; We first invoke the link for da, (κ da), on the scalar
;;   da
;; the multiplicative accumulator
;;   (* 1.0 z)
;; which we explain below, and the gradient state
;;   σ
;; to obtain
;;   the new gradient state σ-hat

;; We next invoke the link for db, (κ db), on the scalar
;;   db
;; the multiplicative accumulator
;;   (* 1.0 z)
;; which we explain below, and the gradient state
;;   σ-hat
;; to obtain
;;   the resultant gradient state that is returned from the
;;   link

;; Now let’s look at the multiplicative accumulators. When
;; we walk down the links of da and db, the multiplicative
;; accumulator is the product of the current accumulator z
;; and the gradient of the primitive.

;; The gradients of addition, with respect to the argument
;; whose chain we are walking down, as in frame 10, are
;; both
1.0

;; So, this link begins the walk down the chains for da and
;; for db with multiplicative accumulators
;;   (* 1.0 z) for da
;; and
;;   (* 1.0 z) for db

;; Also, since this link does not end a chain, we do not
;; need to keep track of any gradients for d. Hence, we
;; ignore d.


;;; Similarly, we can define exp-0 and *-0-0
(define exp-0-v1
  (lambda (da)
    (dual (exp (ρ da))
      (lambda (d z σ)
        ((κ da) da (* (exp (ρ da)) z) σ)))))

(∇ exp-0-v1 1)

(define *-0-0-v1
  (lambda (da db)
    (dual (* (ρ da) (ρ db))
      (lambda (d z σ)
        (let ((σ-hat ((κ da) da (* (ρ db) z) σ)))
          ((κ db) db (* (ρ da) z) σ-hat))))))

(define mult-v1
  (lambda (θ)
    (*-0-0-v1 (list-ref θ 0) (list-ref θ 1))))

(∇ mult-v1 (list 2.8 1.2))

;; The patterns for defining primitives are very similar,
;; and can be generalized for the definitions of all our
;; primitives. Let us start with a one-argument
;; primitive. We propose a function prim1 that can be used
;; to define, for example, exp-0.
#;
(define exp-0-v2
  (prim1 exp
    (lambda (ra z)
      (* (exp ra) z))))

;; Here, exp is the function that will accept one real
;; number argument and produce the real part of the answer,
;; which will be a dual.

;; In this definition, prim1 accepts two function
;; arguments. The first is the function that defines the
;; real part of the dual. Hence we refer to this as the
;; ρ-function of the primitive.

;; The second function defines how the body of the link
;; should behave. In other words, it incorporates the
;; formula for the gradient. Hence we refer to this as the
;; ∇-function of the primitive. The second function expects
;; two arguments and is responsible for computing the
;; gradient. The first, ra, is the same real argument that
;; is passed when calculating the real part. The second is
;; the multiplicative accumulator that will be passed into
;; the link.

;; An invocation of prim1 returns a function that accepts a
;; dual argument and returns a corresponding dual with a
;; properly constructed link.

;; The two arguments ρ-fn (for ρ-function), and ∇-fn (for
;; ∇-function) are used to produce the real part and the
;; gradient, respectively. It returns a function that
;; accepts one dual argument da and produces a dual.

;; The real part of the produced dual is determined by
;; invoking ρ-fn on the real part of da.

;; The link of the dual has a body that invokes ∇-fn with
;; the real part of da and z, and passes the result down
;; the link of da.
(define prim1
  (lambda (ρ-fn ∇-fn)
    (lambda (da)
      (let ((ra (ρ da)))
        (dual (ρ-fn ra)
          (lambda (d z σ)
            (let ((ga (∇-fn ra z)))
              ((κ da) da ga σ))))))))

;; Then we can define
(define exp-0
  (prim1 exp
    (lambda (ra z)
      (* (exp ra) z))))

;; And similarly, here is prim2. The biggest difference,
;; aside from the additional argument to ρ-fn and ∇-fn, is
;; that we use Scheme’s multiple-value return feature to
;; receive two gradients from ∇-fn, one each for da and db.
;; Here we use let-values to bind multiple values returned
;; by ∇-fn. So, here ∇-fn should be a function that returns
;; multiple values.
(define prim2
  (lambda (ρ-fn ∇-fn)
    (lambda (da db)
      (let ((ra (ρ da))
            (rb (ρ db)))
        (dual (ρ-fn ra rb)
          (lambda (d z σ)
            (let-values (((ga gb) (∇-fn ra rb z)))
              (let ((σ-hat ((κ da) da ga σ)))
                ((κ da) db gb σ-hat)))))))))

;; Then we can define +-0-0 and *-0-0.
(define +-0-0
  (prim2 +
    (lambda (ra rb z)
      (values (* 1.0 z) (* 1.0 z)))))

(define *-0-0
  (prim2 +
    (lambda (ra rb z)
      (values (* rb z) (* ra z)))))

(define mult
  (lambda (θ)
    (*-0-0 (list-ref θ 0) (list-ref θ 1))))

(∇ mult (list 2.8 1.2))

;; Now we define some comparison functions, so that we can
;; also compare duals.
(define comparator
  (lambda (f)
    (lambda (da db)
      (f (ρ da) (ρ db)))))

(define <-0-0 (comparator <))
(define >-0-0 (comparator >))
(define <=-0-0 (comparator <=))
(define >=-0-0 (comparator >=))
(define =-0-0 (comparator =))

(<-0-0 (dual* 1.0) (dual* 0.5))

;; And here are
(define --0-0
  (prim2 -
    (lambda (ra rb z)
      (values z (- z)))))

(∇ (lambda (θ) (--0-0 (list-ref θ 0) (list-ref θ 1)))
   (list 4.0 2.0))

(define /-0-0
  (prim2 /
    (lambda (ra rb z)
      (values (/ z rb)
        (* (/ (* -1 ra) (* rb rb)) z)))))

(∇ (lambda (θ) (/-0-0 (list-ref θ 0) (list-ref θ 1)))
   (list 4.0 2.0))

(define log-0-0
  (prim1 log
    (lambda (ra z)
      (* (/ 1 ra) z))))

(∇ log-0-0 8)

(define expt-0-0
  (prim2 expt
    (λ (ra rb z)
      (values (* z (* rb (expt ra (- rb 1))))
        (* z (* (expt ra rb) (log ra)))))))

(∇ (lambda (a) (expt-0-0 a 3)) 3)

(define sqrt-0
  (prim1 sqrt
    (lambda (ra z)
      (* (* 0.5 (/ 1 (sqrt ra))) z))))

(∇ sqrt-0 64)

(∇ (λ (x)
     (let ((a (vector-ref (list-ref x 0) 0))
           (b (list-ref x 1)))
       (+-0-0 (*-0-0 a b) (/-0-0 a 12))))
   (list (vector 5.0) 3.0))
