# Group Identification

 - João Marto, 102174, joaopomarto@tecnico.ulisboa.pt
 - Miguel Ferreira, 95644, miguel.carmo.ferreira@tecnico.ulisboa.pt
 - Tomás Duarte, 111002, tomas.p.duarte@tecnico.ulisboa.pt

# Implemented Features

 - Imp.v
    - Extended the *com* datatype with 2 new constructors: *CNonDet* and *CCondGuard*
    - Created 2 new notations for the new datatypes
    - Defined p1 and p2
 - Interpreter.v
    - Created new notation *CHECKSUC* for cleaner code in ceval_step
    - Added ceval_step cases for new constructs
    - *p1_equals_p2* proof
    - *ceval_step_more* proof - unfinished
 - RelationalEvaluation.v
    - Added 4 new rules for new notations in ceval
    - *ceval_example_if* proof
    - *ceval_example_guard1* proof
    - *ceval_example_guard2* proof
    - *ceval_example_guard3* proof - not done
    - *ceval_example_guard4* proof - not done
    - *cequiv_ex1* proof - not done
    - *cequiv_ex2* proof - not done
    - *choice_idempotent* proof
    - *choice_comm* proof
    - *choice_assoc* proof - unfinished
    - *choice_seq_distr_l* proof - unfinished
    - *choice_congruence* proof
 - ImpParser.v
    - Added parsing for new notations in parseSimpleCommand

# Extras

 - Added error messages to *Fail* and *OutOfGas* and used those in interpreter

