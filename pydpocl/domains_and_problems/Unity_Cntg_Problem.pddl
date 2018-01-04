(define (problem unity-simple-problem)
  (:domain unity-simple-domain)
  (:objects bandit - person
            duel-right right far-right - place
			)
  (:init (at bandit right)
		 )
  (:goal (and
            (bel (at bandit far-right))
		 )
  )
)