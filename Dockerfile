FROM rocq/rocq-prover:9.1-native-flambda
RUN eval $(opam env "--switch=${COMPILER}" --set-switch)
RUN opam update -y
RUN opam install -y vsrocq-language-server
RUN mkdir /home/rocq/ProofAssistantSeminar
# ADD https://github.com/rocq-community/ProofAssistantSeminar.git /home/rocq/ProofAssistantSeminar
ADD . /home/rocq/ProofAssistantSeminar
USER root
RUN chown -R rocq:rocq ProofAssistantSeminar
USER rocq
RUN rm -rf ProofAssistantSeminar/.git
RUN opam pin ProofAssistantSeminar -yn
RUN opam install -y --deps-only rocq-ProofAssistantSeminar-dev
