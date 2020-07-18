{--
 -- Base.hs
 -- Basic axioms derived from the logic laws
 --}
module HML.Logic.Predicates.Axioms.Base where

import HML.Logic.Predicates.PredicateLogicLaws
import HML.Logic.Predicates.PredicateProofGraph

{- ---------- Some standard axioms ---------- -}

standardAxioms :: [AxiomSchema]
standardAxioms = [equivalenceAxiom
                 ,implicationAxiom
                 ,doubleNegationAxiom
                 ,idempotentAndAxiom
                 ,idempotentOrAxiom
                 ,commutativeAndAxiom
                 ,commutativeOrAxiom
                 ,associativeAndAxiom
                 ,associativeOrAxiom
                 ,distributiveAndAxiom
                 ,distributiveOrAxiom
                 ,deMorgansAndAxiom
                 ,deMorgansOrAxiom
                 ,identityAndAxiom
                 ,identityOrAxiom
                 ,annihilationAndAxiom
                 ,annihilationOrAxiom
                 ,inverseAndAxiom
                 ,inverseOrAxiom
                 ,absorptionAndAxiom
                 ,absorptionOrAxiom
                 ,deMorgansForallAxiom
                 ,deMorgansExistsAxiom
                 ,swapForallAxiom
                 ,swapExistsAxiom]

equivalenceAxiom = AxiomSchema { schemaName = "equivalence"
                               , schemaGroup = "Base"
                               , schemaDescription = ""
                               , schema = PredicateSchema equivalenceLaw }

implicationAxiom = AxiomSchema { schemaName = "implication"
                               , schemaGroup = "Base"
                               , schemaDescription = ""
                               , schema = PredicateSchema implicationLaw }

doubleNegationAxiom = AxiomSchema { schemaName = "doubleNegation"
                                  , schemaGroup = "Base"
                                  , schemaDescription = ""
                                  , schema = PredicateSchema doubleNegationLaw }

idempotentAndAxiom = AxiomSchema { schemaName = "idempotentAnd"
                                 , schemaGroup = "Base"
                                 , schemaDescription = ""
                                 , schema = PredicateSchema idempotentAndLaw }

idempotentOrAxiom = AxiomSchema { schemaName = "idempotentOr"
                                , schemaGroup = "Base"
                                , schemaDescription = ""
                                , schema = PredicateSchema idempotentOrLaw }

commutativeAndAxiom = AxiomSchema { schemaName = "commutativeAnd"
                                  , schemaGroup = "Base"
                                  , schemaDescription = ""
                                  , schema = PredicateSchema commutativeAndLaw }

commutativeOrAxiom = AxiomSchema { schemaName = "commutativeOr"
                                 , schemaGroup = "Base"
                                 , schemaDescription = ""
                                 , schema = PredicateSchema commutativeOrLaw }

associativeAndAxiom = AxiomSchema { schemaName = "associativeAnd"
                                  , schemaGroup = "Base"
                                  , schemaDescription = ""
                                  , schema = PredicateSchema associativeAndLaw }

associativeOrAxiom = AxiomSchema { schemaName = "associativeOr"
                                 , schemaGroup = "Base"
                                 , schemaDescription = ""
                                 , schema = PredicateSchema associativeOrLaw }

distributiveAndAxiom = AxiomSchema { schemaName = "distributiveAnd"
                                   , schemaGroup = "Base"
                                   , schemaDescription = ""
                                   , schema = PredicateSchema distributiveAndLaw }

distributiveOrAxiom = AxiomSchema { schemaName = "distributiveOr"
                                  , schemaGroup = "Base"
                                  , schemaDescription = ""
                                  , schema = PredicateSchema distributiveOrLaw }

deMorgansAndAxiom = AxiomSchema { schemaName = "deMorgansAnd"
                                , schemaGroup = "Base"
                                , schemaDescription = ""
                                , schema = PredicateSchema deMorgansAndLaw }

deMorgansOrAxiom = AxiomSchema { schemaName = "deMorgansOr"
                               , schemaGroup = "Base"
                               , schemaDescription = ""
                               , schema = PredicateSchema deMorgansOrLaw }

identityAndAxiom = AxiomSchema { schemaName = "identityAnd"
                               , schemaGroup = "Base"
                               , schemaDescription = ""
                               , schema = PredicateSchema identityAndLaw }

identityOrAxiom = AxiomSchema { schemaName = "identityOr"
                              , schemaGroup = "Base"
                              , schemaDescription = ""
                              , schema = PredicateSchema identityOrLaw }

annihilationAndAxiom = AxiomSchema { schemaName = "annihilationAnd"
                                   , schemaGroup = "Base"
                                   , schemaDescription = ""
                                   , schema = PredicateSchema annihilationAndLaw }

annihilationOrAxiom = AxiomSchema { schemaName = "annihilationOr"
                                  , schemaGroup = "Base"
                                  , schemaDescription = ""
                                  , schema = PredicateSchema annihilationOrLaw }

inverseAndAxiom = AxiomSchema { schemaName = "inverseAnd"
                              , schemaGroup = "Base"
                              , schemaDescription = ""
                              , schema = PredicateSchema inverseAndLaw }

inverseOrAxiom = AxiomSchema { schemaName = "inverseOr"
                             , schemaGroup = "Base"
                             , schemaDescription = ""
                             , schema = PredicateSchema inverseOrLaw }

absorptionAndAxiom = AxiomSchema { schemaName = "absorptionAnd"
                                 , schemaGroup = "Base"
                                 , schemaDescription = ""
                                 , schema = PredicateSchema absorptionAndLaw }

absorptionOrAxiom = AxiomSchema { schemaName = "absorptionOr"
                                , schemaGroup = "Base"
                                , schemaDescription = ""
                                , schema = PredicateSchema absorptionOrLaw }

deMorgansForallAxiom = AxiomSchema { schemaName = "deMorgansForall"
                                   , schemaGroup = "Base"
                                   , schemaDescription = ""
                                   , schema = PredicateSchema deMorgansForallLaw }

deMorgansExistsAxiom = AxiomSchema { schemaName = "deMorgansExists"
                                   , schemaGroup = "Base"
                                   , schemaDescription = ""
                                   , schema = PredicateSchema deMorgansExistsLaw }

swapForallAxiom = AxiomSchema { schemaName = "swapForall"
                              , schemaGroup = "Base"
                              , schemaDescription = ""
                              , schema = PredicateSchema swapForallLaw }

swapExistsAxiom = AxiomSchema { schemaName = "swapExists"
                              , schemaGroup = "Base"
                              , schemaDescription = ""
                              , schema = PredicateSchema swapExistsLaw }


