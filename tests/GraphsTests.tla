------------------------- MODULE GraphsTests -------------------------
EXTENDS Graphs, TLCExt

ASSUME LET T == INSTANCE TLC IN T!PrintT("GraphsTests")

ASSUME AssertEq(SimplePath([edge|-> {}, node |-> {}]), {})
ASSUME AssertEq(SimplePath([edge|-> {}, node |-> {1,2,3}]), {<<1>>, <<2>>, <<3>>})
ASSUME AssertEq(SimplePath([edge|-> {<<1,2>>, <<2,3>>}, node |-> {1,2,3}]), 
            { <<1>>, <<2>>, <<3>>, <<1,2>>, <<2,3>>, <<1,2,3>> } )
                
=====================================================================