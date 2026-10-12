/-compile an executable with the line below.
run it in the terminal using >lean --run helloworldexe.lean
-/


-- this is the mentioned line
def main : IO Unit := IO.println "Hello, world! That \nwas easy."
