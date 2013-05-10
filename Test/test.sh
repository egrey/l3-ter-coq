#Teste un type simple
../comp < bit.ml4 > bit.v ; coqc bit.v
#Teste la prise en compte des arguments d'un constructeur
../comp < natural.ml4 > natural.v ; coqc natural.v
#Teste un type générique
../comp < stack.ml4 > stack.v ; coqc stack.v
#Teste la prise en compte des tuples
../comp < tree.ml4 > tree.v ; coqc tree.v
#Teste la prise en compte des fonctions
#../comp < list.ml4 > list.v ; coqc list.v
#Supprime les fichiers générés par coqc
rm -f *.vo *.glob
