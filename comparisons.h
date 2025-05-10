#ifndef COMPARISONS_H
#define COMPARISONS_H

// Declaração da variável global para contar comparações
extern int comparisons;

// Função para zerar o contador de comparações
void resetComparisons();

// Função para retornar o número atual de comparações
int getComparisons();

// Funções de comparação - sempre incrementam o número de comparações
int ehMaior(int a, int b);
int ehMenor(int a, int b);
int ehIgual(int a, int b);
int ehMaiorOuIgual(int a, int b);
int ehMenorOuIgual(int a, int b);
int ehDiferente(int a, int b);

#endif // COMPARISONS_H
