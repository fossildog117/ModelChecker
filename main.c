#include <stdio.h>
#include <string.h>   /* for all the new-fangled string functions */
#include <stdlib.h>     /* malloc, free, rand */
#include <stdbool.h>

#define TRUE = 1
#define FALSE = 0

/*  The main program calls procedures parse, partone, parttwo and bin which are not implemented here.
 */

int Fsize=50;  /*big enough for our formulas*/

int no_edges;
int no_nodes;

int numberOfBrackets = 0;
int lengthOfString = 0;
int store = 0;

int parse(char *g);
char bin(char *g);
char *partone(char *g);
char *parttwo(char *g);
char *string[];

char *connectives[];
int no_connectives = 0;
bool var_assign = true;
int trueCount = 0;

int eval(char *nm, int edges[no_edges][2], int size, int V[3])
/*this method takes a formula, the list of edges of a graph, the number of vertices and a variable assignment.  It then evaluates the formula and returns 1 or 0 as appropriate.  */
{
    
    if (*nm == '(') {
        for (int i = 0; i < no_connectives; i++) {
            eval(nm, edges, no_nodes, V);
        }
    }
    
    if (*nm == 'X' && var_assign == true) {
        if (*(nm + 2) == *(nm + 3)) {
            for (int i = 0; i < no_edges; i++) {
                if (edges[i][0] == edges[i][1]) {
                    return 1;
                }
            }
        }
        if (*(nm + 2) == 'x') {
            if (*(nm + 3) == 'y') {
                for (int i = 0; i < no_edges; i++) {
                    if (edges[i][0] == V[0]) {
                        if (edges[i][1] == V[1]) {
                            return 1;
                        }
                    }
                }
                return 0;
            }
            if (*(nm + 3) == 'z') {
                for (int i = 0; i < no_edges; i++) {
                    if (edges[i][0] == V[0]) {
                        if (edges[i][1] == V[2]) {
                            return 1;
                        }
                    }
                }
            }
        }
        
        if (*(nm + 2) == 'y') {
            if (*(nm + 3) == 'x') {
                for (int i = 0; i < no_edges; i++) {
                    if (edges[i][0] == V[1]) {
                        if (edges[i][1] == V[0]) {
                            return 1;
                        }
                    }
                }
                return 0;
            }
            if (*(nm + 3) == 'z') {
                for (int i = 0; i < no_edges; i++) {
                    if (edges[i][0] == V[1]) {
                        if (edges[i][1] == V[2]) {
                            return 1;
                        }
                    }
                }
            }
        }
        
        if (*(nm + 2) == 'z') {
            if (*(nm + 3) == 'x') {
                for (int i = 0; i < no_edges; i++) {
                    if (edges[i][0] == V[2]) {
                        if (edges[i][1] == V[0]) {
                            return 1;
                        }
                    }
                }
                return 0;
            }
            if (*(nm + 3) == 'y') {
                for (int i = 0; i < no_edges; i++) {
                    if (edges[i][0] == V[2]) {
                        if (edges[i][1] == V[1]) {
                            return 1;
                        }
                    }
                }
            }
        }
    }
    
    //
    // Negation
    //
    
    if (*nm == '-') {
        if (eval((nm + 1), edges, no_nodes, V) == 1) {
            return 0;
        }
        
        if (eval((nm + 1), edges, no_nodes, V) == 0) {
            return 1;
        }
    }
    
    //
    // Universal Quantifier
    //
    
    if (*nm == 'A') {
        var_assign = false;
        
        // AxX[xy]
        if (*(nm+2) == 'X') {
            if (*(nm+1) == *(nm+4)) {
                for (int i = 0; i < no_nodes; i++) {
                    for (int j = 0; j < no_edges; j++) {
                        if (i == edges[j][0]) {
                            trueCount++;
                            break;
                        
                        }
                    }
                }
            }
            if (*(nm+1) == *(nm+5)) {
                for (int i = 0; i < no_nodes; i++) {
                    for (int j = 0; j < no_edges; j++) {
                        if (i == edges[j][1]) {
                            trueCount++;
                            break;
                            
                        }
                    }
                }
            }
            if (trueCount == no_nodes) {
                trueCount = 0;
                return 1;
            }
            trueCount = 0;
        }
        
        // AxAyX[xy]
        if (*(nm+2) == 'A') {
            if (no_edges >= no_nodes * no_nodes) {
                return 1;
            }
        }
        
        // AxEyX[xy]
        if (*(nm+2) == 'E') {
            if (*(nm+6) == *(nm+1) && *(nm+3) == *(nm+7)) {
                for (int i = 0; i < no_nodes; i++) {
                    for (int j = 0; j < no_edges; j++) {
                        if (edges[j][0] == i) {
                            trueCount++;
                            break;
                        }
                    }
                }
            }
            if (*(nm+7) == *(nm+1) && *(nm+6) == *(nm+3)) {
                for (int i = 0; i < no_nodes; i++) {
                    for (int j = 0; j < no_edges; j++) {
                        if (edges[j][1] == i) {
                            trueCount++;
                            break;
                        }
                    }
                }
            }
            if (trueCount == no_nodes) {
                trueCount = 0;
                return 1;
            }
        }
    }
    
    //
    // Extensial Formula
    //
    
    if (*nm == 'E') {
        var_assign = false;
        
        //ExX[xy]
        if (*(nm+2) == 'X') {
            if(*(nm+1) == *(nm+4)) {
                for (int i = 0; i < no_nodes; i++) {
                    for (int j = 0; j < no_edges; j++) {
                        if (edges[j][0] == i) {
                            return 1;
                        }
                    }
                }
            }
            if(*(nm+1) == *(nm+5)) {
                for (int i = 0; i < no_nodes; i++) {
                    for (int j = 0; j < no_edges; j++) {
                        if (edges[j][1] == i) {
                            return 1;
                        }
                    }
                }
            }
        }
        
        // ExAy[xy]
        if (*(nm+2) == 'A') {
            if(*(nm+1) == *(nm+6)) {
                for (int i = 0; i < no_nodes; i++) {
                    for (int j = 0; j < no_edges; j++) {
                        if (edges[j][0] == i) {
                            trueCount++;
                        }
                    }
                    if (trueCount == no_nodes) {
                        trueCount = 0;
                        return 1;
                    }
                    trueCount = 0;
                }
            }
            if(*(nm+1) == *(nm+7)) {
                for (int i = 0; i < no_nodes; i++) {
                    for (int j = 0; j < no_edges; j++) {
                        if (edges[j][1] == i) {
                            trueCount++;
                        }
                    }
                    if (trueCount == no_nodes) {
                        trueCount = 0;
                        return 1;
                    }
                    trueCount = 0;
                }
            }
        }
        
        // ExEyX[xy]
        if (*(nm+2) == 'E') {
            if(*(nm+1) == *(nm+4)) {
                for (int i = 0; i < no_nodes; i++) {
                    for (int j = 0; j < no_edges; j++) {
                        if (edges[j][0] == i) {
                            return 1;
                        }
                    }
                }
            }
            if(*(nm+1) == *(nm+5)) {
                for (int i = 0; i < no_nodes; i++) {
                    for (int j = 0; j < no_edges; j++) {
                        if (edges[j][1] == i) {
                            return 1;
                        }
                    }
                }
            }
        }
    }
    
    return 0;
}

int main()
{
    /*Input a string and check if its a formula*/
    char *name=malloc(Fsize);
    printf("Enter a formula: ");
    scanf("%s", name);
    int p=parse(name);
    switch(p)
    {
        case 0: printf("Not a formula \n");break;
        case 1: printf("An atomic formula \n");break;
        case 2: printf("A negated formula \n");break;
        case 3: printf("A binary connective formula \n");break;
        case 4: printf("An existential formula \n");break;
        case 5: printf("A universal quantifier \n");break;
        default: printf("Not a formula \n");break;
    }
    
//    if (p==3) {
//        printf("The first part is %s, the binary connective is %c, the second part is %s", partone(string[0]), bin(name), parttwo(string[1]));
//    }
//    return(1);
    
    /*Input a graph.  No. of nodes, edges, then input each edge.*/
    if (p != 0) {
        printf("How many nodes in the graph?\n");
        scanf(" %d", &no_nodes);
        printf("The nodes are 0, 1, ..., %d\n", no_nodes-1);
        printf("Now the edges\n");
        printf("How many edges?\n");
        scanf(" %d", &no_edges);
        
        int edges[no_edges][2];  /*Store edges in 2D array*/
        int  i, k, j;
        for(i=0;i<no_edges;i++)
        {
            printf("input a pair of nodes (<%d)", no_nodes);
            scanf(" %d", &j);scanf(" %d", &k);
            edges[i][0]=j; edges[i][1]=k;
        }
        
        /*Assign variables x, y, z to nodes */
        int V[3];
        /*Store variable values in array
         value of x in V[0]
         value of y in V[1]
         value of z in V[2] */
        printf("Assign variables x, y, z\n");
        printf("x is ?(<%d)", no_nodes);scanf(" %d", &V[0]);
        printf("y is ?");scanf(" %d", &V[1]);
        printf("z is ?");scanf(" %d", &V[2]);
        
        /*Now check if formula is true in the graph with given variable assignment. */
        if (eval(name, edges, no_nodes,  V)==1) {
            printf("The formula %s is true \n", name);
        } else {
            printf("The formula %s is false \n", name);
        }
        
        free(name);
        
    }
    return(1);
}

int parse(char *g)
/* returns 0 for non-formulas, 1 for atoms, 2 for negations, 3 for binary connective fmlas, 4 for existential and 5 for universal formulas.*/

{
    if (*g == 'X') {
        if (*(g+1) == '[') {
            if (*(g+2) == 'x' || *(g+2) == 'y' || *(g+2) == 'z') {
                if (*(g+3) == 'x' || *(g+3) == 'y' || *(g+3) == 'z') {
                    if (*(g+4) == ']') {
                        if(*(g + 5) == '\0') {
                            return 1;
                        } else {
                            return 0;
                        }
                    }
                    return 0;
                }
                return 0;
            }
            return 0;
        }
        return 0;
    }
    
    if (*g == '-') {
        if (parse(g+1) != 0) {
            return 2;
        }
    }
    
    if (*g == 'E') {
        if (*(g+1) == 'x' || *(g+1) == 'y' || *(g+1) == 'z') {
            if (parse(g+2) > 0) {
                return 4;
            }
        }
    }
    
    if (*g == 'A') {
        if (*(g+1) == 'x' || *(g+1) == 'y' || *(g+1) == 'z') {
            if (parse(g+2) > 0) {
                return 5;
            }
        }
    }
    
    if (*g == '(') {
        numberOfBrackets++;
        lengthOfString++;
        
        bin(g+1);
        
        long len2 = strlen(g) - lengthOfString;
        string[store] = malloc(lengthOfString); // one for the null terminator
        memcpy(string[store], g+1, lengthOfString - 2);
        
        string[store][lengthOfString - 1] = '\0';
        store++;
        
        string[store]= malloc(len2 + 1); // one for the null terminator
        memcpy(string[store], g+lengthOfString, len2 - 1);
        
        string[store][len2 - 1] = '\0';
        store++;
        
        printf("%s, %s \n", string[store - 2], string[store - 1]);
        string[store] = string[store - 1];
        
        lengthOfString = 0;
        numberOfBrackets = 0;
        
        if (parse(string[store - 2]) != 0) {
            
            if (parse(string[store]) != 0) {
                
                return 3;
                
            }
        }
    }
    
    return 0;
}

char *partone(char *g)
/*
 Given a formula (A*B) this should return A
 */
{
    printf("%s \n", g);
    return string[0];
}

char *parttwo(char *g)
/*
 Given a formula (A*B) this should return B
 */
{
    return string[1];
}

char bin(char *g)
/*
 Given a formula (A*B) this should return the character *
 */
{
    
    if (numberOfBrackets == 1) {
        
        if (*g == 'v' || *g == '^' || *g == '>' || *g == '<') {
            
            connectives[no_connectives] = g;
            
            no_connectives++;
            lengthOfString++;
            
            return *g;
        }
    }
    
    if (*g == '(') {
        numberOfBrackets++;
        
    }
    
    if (*g == ')') {
        numberOfBrackets--;
    }
    
    if (lengthOfString == strlen(g)) {
        return 0;
    }
    
    lengthOfString++;
    
    return bin(g+1);
    
}