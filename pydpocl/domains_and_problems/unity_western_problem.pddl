(define (problem unity-western)
  (:domain western-duel-domain)
  (:objects cowboy bandit - person
            far-left left duel-left duel-right right far-right - place
            cowboy-gun bandit-gun - gun
			shooting-distance - distance
			12 - integer
			main-master-shot - virtual-shot-type
			)
  (:init (at cowboy far-left)
		 (at bandit far-right)
         (alive cowboy) (alive bandit)
		 (has cowboy cowboy-gun)
		 (has bandit bandit-gun)
		 (= shooting-distance 12)
		 (bel (at cowboy far-left))
		 (holstered cowboy-gun)
		 (holstered band-gun)
		(distance-between far-left left  18.01)
		(distance-between far-left duel-left  33.56)
		(distance-between far-left duel-right  42.75)
		(distance-between far-left  right  47.27)
		(distance-between far-left  far-right  54.97)
		(distance-between left  far-left  18.01)
		(distance-between left  duel-left  15.58)
		(distance-between left  duel-right  25.56)
		(distance-between left  right  32.74)
		(distance-between left  far-right  44.02)
		(distance-between duel-left  far-left  33.56)
		(distance-between duel-left  left  15.58)
		(distance-between duel-left  duel-right  11.80)
		(distance-between duel-left  right  23.17)
		(distance-between duel-left  far-right  37.86)
		(distance-between duel-right  far-left  42.75)
		(distance-between duel-right  left  25.56)
		(distance-between duel-right  duel-left  11.80)
		(distance-between duel-right  right   13.22)
		(distance-between duel-right  far-right  28.94)
		(distance-between right  far-left  47.27)
		(distance-between right  left  32.74)
		(distance-between right  duel-left  23.17)
		(distance-between right  duel-right  13.22)
		(distance-between right  far-right  15.76)
		(distance-between far-right  far-left  54.97)
		(distance-between far-right  left 44.02)
		(distance-between far-right  duel-left  37.86)
		(distance-between far-right duel-right  28.94)
		(distance-between far-right right  15.76)
		 )
  (:goal (and
              (not (alive bandit))
		 )
  )
)