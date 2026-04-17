FROM rocq/rocq-prover:9.1-native-flambda
RUN eval $(opam env "--switch=${COMPILER}" --set-switch)
RUN opam update -y
RUN ulimit -s 256000
RUN opam install -y vsrocq-language-server
RUN opam install -y rocq-mathcomp-ssreflect
RUN opam install -y rocq-mathcomp-algebra
RUN opam install -y rocq-mathcomp-stdlib
RUN opam install -y rocq-mathcomp-zify
RUN opam install -y rocq-mathcomp-algebra-tactics
RUN mkdir /home/rocq/ProofAssistantSeminar
# ADD https://github.com/rocq-community/ProofAssistantSeminar.git /home/rocq/ProofAssistantSeminar
ADD rocq-ProofAssistantSeminar-dev.opam /home/rocq/ProofAssistantSeminar/rocq-ProofAssistantSeminar-dev.opam
USER root
RUN chown -R rocq:rocq ProofAssistantSeminar
USER rocq
RUN opam pin ProofAssistantSeminar -yn
RUN opam install -y --deps-only rocq-ProofAssistantSeminar-dev
ADD Makefile /home/rocq/ProofAssistantSeminar/Makefile
ADD magic.v /home/rocq/ProofAssistantSeminar/magic.v
ADD nat.v /home/rocq/ProofAssistantSeminar/nat.v
ADD nat_solution.v /home/rocq/ProofAssistantSeminar/nat_solution.v
ADD nat_golf.v /home/rocq/ProofAssistantSeminar/nat_golf.v
ADD ssrnat.v /home/rocq/ProofAssistantSeminar/ssrnat.v
ADD ssrnat_solution.v /home/rocq/ProofAssistantSeminar/ssrnat_solution.v
ADD ssrnat_golf.v /home/rocq/ProofAssistantSeminar/ssrnat_golf.v
