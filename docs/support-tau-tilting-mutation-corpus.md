# Support tau-tilting mutation corpus

Every checking constructor and every `verify()` rejects a targeted mutation:
a non-basic decomposition presented as basic; a pair whose summand count is
off by one; a borrowed `TauRigidModule`; an omitted vertex outside the support
complement; a `NonTauRigidWitness` whose morphism is zero; an approximation
witness missing one factorization; a minimality witness whose `K_f` basis
leaves `rad End(B)`; a mutation witness whose target is not a support
tau-tilting pair; a closure witness with a missing slot, a duplicated vertex,
a broken involution, or a graph disconnected from `(A, 0)`.
