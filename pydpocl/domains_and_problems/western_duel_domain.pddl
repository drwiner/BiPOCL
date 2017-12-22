(define (domain western-duel-domain)

    (:types   s-elmnt plan-elmnt intrvl cam-param - object
		literal step - plan-elmnt
		movable-thing - story-element
		person thing - movable-thing
		place - s-elmnt
		gun - thing)
		
    (:predicates
		(has ?c - person ?t - thing)
        (at ?thing - movable-thing ?place - object)
        (= ?o1 ?o2 - object)
		(facing ?c1 ?c2 - person)
		(alive ?c - person)
		(holstered ?g - gun)
        )
                    
    (:action strut
        :parameters (?c - person ?p1 ?p2 - place)
        :precondition (and (at ?c ?p1) (alive ?c))
        :effect(and (not (at ?c ?p1)) (at ?c ?p2)))
                    
    (:action drive
        :parameters (?person - person ?car - car ?from ?to - place)
        :precondition (and (at ?car ?from)
                        (not (= ?from ?to))
                           (in ?person ?car))
        :effect(and (at ?car ?to)
                    (not (at ?car ?from))))
                    
    (:action get-out-of-car
        :parameters (?person - person ?car - car ?place - place)
        :precondition (and (at ?car ?place)
                           (in ?person ?car))
        :effect (and (at ?person ?place)
                    (not (in ?person ?car))))
                    
    (:action buy-tickets
        :parameters (?person - person)
        :precondition ()
        :effect (has-ticket ?person))
        
    (:action board-plane
        :parameters (?person - person ?plane - plane ?place - place)
        :precondition (and (at ?person ?place)
                           (at ?plane ?place)
                           (has-ticket ?person))
        :effect(and (in ?person ?plane)
                    (not(at ?person ?place))
                    (not(has-ticket ?person))))
                    
    (:action fly
        :parameters (?person - person ?plane - plane ?from ?to - place)
        :precondition (and (at ?plane ?from) (not (= ?from ?to))
                            (in ?person ?plane))
        :effect(and (at ?plane ?to)
                   (not (at ?plane ?from))))
                   
    (:action deplane
        :parameters (?person - person ?plane - plane ?place - place)
        :precondition (and (at ?plane ?place)
                           (in ?person ?plane))
        :effect (and (at ?person ?place)
                     (not (in ?person ?plane))))

    (:action travel-by-car
        :parameters (?person - person ?from ?to - place)
		:precondition (and (at ?person ?from) (not (= ?from ?to)))
        :effect(and (at ?person ?to)
                    (not (at ?person ?from)))
		:decomp(
			:sub-params (?car - car ?s1 ?s2 ?s3 - step)
			:requirements( and
				(= ?s1 (get-in-car ?person ?car ?from))
                (= ?s2 (drive ?person ?car ?from ?to))
                (= ?s3 (get-out-of-car ?person ?car ?to))
				(linked-by ?s1 ?s2 (in ?person ?car))
				(linked-by ?s1 ?s3 (in ?person ?car))
				(linked-by ?s2 ?s3 (at ?car ?to)))))

    (:action travel-by-plane
        :parameters (?person - person ?from ?to - place)
		:precondition (and (at ?person ?from) (not (= ?from ?to)))
        :effect(and (at ?person ?to)
                    (not (at ?person ?from)))
		:decomp(
			:sub-params (?plane - plane
				?s1 ?s2 ?s3 ?s4 - step)
			:requirements(and
				(= ?s1 (buy-tickets ?person))
                (= ?s2 (board-plane ?person ?plane ?from))
                (= ?s3 (fly ?person ?plane ?from ?to))
                (= ?s4 (deplane ?person ?plane ?to))
				(linked-by ?s1 ?s2 (has-ticket ?person))
				(linked-by ?s2 ?s3 (in ?person ?plane))
				(linked-by ?s2 ?s4 (in ?person ?plane))
				(linked-by ?s3 ?s4 (at ?plane ?to)))))

	(:action travel
	    :parameters (?person - person ?to - place)
	    :precondition ()
	    :effect(and (at ?person ?to))
	    :decomp (
	        :sub-params(?travel-step - step)
	        :requirements(and
	            (effect ?travel-step (at ?person ?to)))))
)