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
 - RelationalEvaluation.v
    - Added 4 new rules for new notations in ceval
 - ImpParser.v
    - Added parsing for new notations in parseSimpleCommand

# Extras

