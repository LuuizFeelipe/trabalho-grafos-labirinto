#include "comparisons.h"

// Definição da variável global
int comparisons = 0;

// Função para zerar o contador de comparações
void resetComparisons() {
    comparisons = 0;
}

// Função para retornar o número atual de comparações
int getComparisons() {
    return comparisons;
}

// Funções de comparação - sempre incrementam o número de comparações
int ehMaior(int a, int b) {
    comparisons++;
    return a > b;
}

int ehMenor(int a, int b) {
    comparisons++;
    return a < b;
}

int ehIgual(int a, int b) {
    comparisons++;
    return a == b;
}

int ehMaiorOuIgual(int a, int b) {
    comparisons++;
    return a >= b;
}

int ehMenorOuIgual(int a, int b) {
    comparisons++;
    return a <= b;
}

int ehDiferente(int a, int b) {
    comparisons++;
    return a != b;
}
