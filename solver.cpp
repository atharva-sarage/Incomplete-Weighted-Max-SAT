/******************************************
*    AUTHOR:         Atharva Sarage       *
*    INSTITUITION:   IIT HYDERABAD        *
******************************************/
#include<bits/stdc++.h>
time_t timeStart;
using namespace std;
int totalClauses,totalVariables; // These are initialized in main()
inline int getvariable(int i){ // returns variable corresponding to literal
    return (i+1)/2;
}
/**
 * Class for representing a Clause in the input
 */
class clause{
    private:
        bool tautology=false; // This is true when a clause contains a literal and its negation.
        int totalLiterals=0;  // Count of total number of literals in the clause
        int weight;
    public:
        vector<int>literals;  // This vector stores all the literals 
        clause(int weight){this->weight=weight;}            // default constructor
        // Create a clause object with one literal 
        clause(int unitLiteral,int weight){
            literals.emplace_back(unitLiteral); // emplace_back is faster than push_back
            this->weight=weight;
        }    
        int getVariable(int idx){return getvariable(literals[idx]);}
        int getWeight(){return weight;}
        /**
        * addLiteral function adds a literal to the clause
        * while adding it increments the totalLiterals
        * and also checks for its negated literal, if it
        * finds it it sets tautology to true
        * positive literal are represented by even numbers +1->2,+2->4,...
        * negative literal are represented by odd numbers -1->1,-2->3,...
        */
        inline void addLiteral(int x){
            totalLiterals++;
            if(x<0){
                // convert negative literal to corresponding odd number
                literals.emplace_back(-2*x-1);
                tautology|=(find(literals.begin(),literals.end(),2*x)!=literals.end()); // bitwise or 
            }
            else{
                // convert positive literal to corresponding even number
                literals.emplace_back(2*x);
                tautology|=(find(literals.begin(),literals.end(),-2*x-1)!=literals.end());
            }
        }
        // Returns total Literals
        int getCountLiteralsInClause(){
            return totalLiterals;
        }
        // Returns whether clause is a tautology
        bool isTautology(){
            return tautology;
        }
           // prints a clause
        void printClause(){
            cout<<weight<<": ";
            for(auto lit:literals){
                cout<<lit<<" ";
            }
            cout<<endl;
        }
};

/**
 * Clause clauseSet
 * Stores all the clauses information
 */
class clauseSet{
    public:
        vector <clause> clauses; // vector of clause
        // for each literal we keep a pointer to a list(vector) which stores in which clauses it occurs.
        // state stores the initial state of all the clauses
        clauseSet(){                 
            // clauses are also 1 indexed put a dummy clause at 0 index
            clauses.emplace_back(clause(0,0));     
        }
        int getTotalWeight(){
            int totalWeight=0;
            for(auto clause:clauses)
                totalWeight+=clause.getWeight();
            return totalWeight;
        }
        /**
         * Add clause method add a clause to the clauseset only if it not
         * a tautology. It then updates countClause and the literalClauseMap
         */
        clause getClause(int idx){
            return clauses[idx];
        }
        int getClauseCount(int idx){
            return clauses[idx].literals.size();
        }
        int getClauseWeight(int idx){
            return clauses[idx].getWeight();
        }
        void addClause(clause cs){
            if(cs.isTautology())
                return;
            else
                clauses.emplace_back(cs); // add to clauses                                           
        }       
        // helper function to print all the indices where this literal occurs
};
/**
 * Local Search Solver Class
 */
class Solver{
    private:
        clauseSet clauses; // Store all clauses   
        /**
         * Tabulength is no of flips a variable must wait before flipping again;
         * maxFlips is max number of flips in given iteration
         * maxIter is max number of iteration.
         * We reset assignment at the start of every iteration
         */     
        int tabuLength,maxFlips,maxIter;         
        int currentScore=0; // current weight of satisfied clauses
        int threshold; // if current score crosses threshold we stop
        double noise=0.1; // hyper parameter for algorithm
        pair<int,vector<bool>> bestAnswer;
        vector <bool> assignment; // keeps track of current Assignment
        vector <bool> currentClauseStatus; // keeps track of currently which clauses are satisfied
        vector <int> UNSATClauses; // keeps track of currently unsatisfied clauses
        vector <int> history;  // keeps track of last flip
        
    public: 
        // constructor
        Solver(clauseSet clauses,int tabuLength,int maxFlips,int maxIter){
            history.resize(totalVariables+5);
            this->clauses=clauses;
            this->tabuLength = tabuLength;
            this->maxFlips =  maxFlips;
            this->maxIter = maxIter;
            threshold = clauses.getTotalWeight()*0.99;  // set threshold
            generateRandomAssignment(); 
       }
        /**
         * solve() function implements WALK SAT Algorithm with TABU(gap between flip of same variables)
         * returns {score,corresponding assignment}
         */
        pair<int,vector<bool>> solve(){
            for(int itr=1;itr<=maxIter;itr++){    
                generateRandomAssignment();   
                for(int flips=1;flips<=maxFlips;flips++){
                    bool res=checkTimeStopExecution();    // is excedded 55 sec stop               
                    if(res)return bestAnswer;
                    updateStatus(); // updates score and unsat clauses                                     
                    // if score above threshold we return current answer
                    if(currentScore>threshold || UNSATClauses.size()==0){
                        updateScore(currentScore);
                        return bestAnswer;;
                    }
                    /**
                     * This while loop chooses which variable to flip
                     * ALG:
                     *  Select uniformly at random any Unsatisfied clause
                     *  with probablity noise choose any literal in that clause and flip it
                     *  with probablity 1-noise choose literal that minimises weights of
                     *  clause which satisfied before and are unsatisfied clauses.
                     *  If there is a tie then pick a variable which maximises weights of
                     *  clauses which are satisfied and were previously unsatisfied.
                     *  But if difference between preivious flip and cuurent flip is less
                     *  than tabulength we repeat again.
                     */
                    
                    while(1){
                        // choose clause from unsat clauses at random
                        int randomUNSATClauseIdx = getRandonInRange(0,UNSATClauses.size()-1);  
                        pair<pair<int,int>,int> minWeightLiteral={{INT_MAX,INT_MAX},0};      
                        // choose the best literal satisfying the condition mentioned in algo
                        for(auto literal:clauses.getClause(UNSATClauses[randomUNSATClauseIdx]).literals){
                            pair<int,int> res=unsatisfiedWeight(literal);               
                            minWeightLiteral=min(minWeightLiteral,{res,getvariable(literal)});            
                        }

                        double prob=(double)(rand())/(RAND_MAX);
                        // with probablity 1-noise choose best one 
                        if((prob - noise)>=1e-6 ){
                            if(history[minWeightLiteral.second]==-1 || flips-history[minWeightLiteral.second]>tabuLength){
                                // flip assignment and set history to current flip number
                                assignment[minWeightLiteral.second]=assignment[minWeightLiteral.second]^true;
                                history[minWeightLiteral.second]=flips;
                                break;
                            }
                        }
                        // with probablity noise choose any variable it selected clause
                        else {
                            int randomVarIdx = getRandonInRange(0,clauses.getClauseCount(UNSATClauses[randomUNSATClauseIdx])-1);
                            int randomVar = clauses.getClause(UNSATClauses[randomUNSATClauseIdx]).getVariable(randomVarIdx);
                            if(history[randomVar]==-1 || flips-history[randomVar]>tabuLength){
                                assignment[randomVar]=true^assignment[randomVar]; 
                                history[randomVar]=flips;
                                break;
                            }
                        }
                    }
                }
            }
        return bestAnswer;
        }
        // creates a random assignment
        void generateRandomAssignment(){
            assignment.clear();
            for(int i=0;i<=totalVariables;i++){
                history[i]=-1; // not flipped yet
                if(rand()%2==0)
                    assignment.push_back(true);                        
                else
                    assignment.push_back(false);                                      
            }
        }
        // updates current score and unsatclasuse vector.
        void updateStatus(){
            vector<bool> tempClauseStatus;
            // get clauses status which are satisfied , which are unsat under current assignment
            getCurrentClauseStatus(assignment,tempClauseStatus);
            currentScore=0;
            UNSATClauses.clear();
            for(int i=1;i<=totalClauses;i++){           
                if(!tempClauseStatus[i])
                    UNSATClauses.push_back(i);
                else            
                    currentScore+=clauses.getClause(i).getWeight();            
            }
            currentClauseStatus=tempClauseStatus;
            updateScore(currentScore);      
        }
        // updates score
        void updateScore(int currentScore){
            if(bestAnswer.first<currentScore)
                cout<<"o "<<currentScore<<endl;
            bestAnswer=max(bestAnswer,{currentScore,assignment});
        }
         // get clauses status which are satisfied , which are unsat under current assignment
        void getCurrentClauseStatus(vector<bool> assignment_,vector<bool>&currentStatus){
            currentStatus.push_back(false);
            for(int i=1;i<=totalClauses;i++){
                currentStatus.push_back(checkSatisfied(clauses.getClause(i),assignment_));
            }
        }
        // checks whether is satisfied under current assignment
        bool checkSatisfied(clause cl,vector<bool>assignment_l){
            for(auto lit:cl.literals){   
                int var = getvariable(lit);
                if((lit%2==0 && assignment_l[var]==true) || (lit%2==1 && assignment_l[var]==false) )
                    return true;
            }
            return false;
        }
        // returns a pair {reducedWeight,-increased Weight} when a variable is flipped
        // differnce is calculated between previous and current assignment(flipped).
        pair<int,int> unsatisfiedWeight(int literal){
            int variable = getvariable(literal);
            int reducedWeight=0,increasedWeight=0;
            vector<bool>tempAssignment = assignment;
            tempAssignment[variable]=true^tempAssignment[variable];        
            // tempClauseStatus stores status of clauses(which are satisfied, which are not)
            // under flipped assignment
            vector <bool> tempClauseStatus;
            getCurrentClauseStatus(tempAssignment,tempClauseStatus);      
            for(int i=1;i<=totalClauses;i++){            
                // earlier refers to assignment before flipping
                // clause satisfied earlier but not now
                if(tempClauseStatus[i]==false && currentClauseStatus[i]==true){
                    reducedWeight+=clauses.getClauseWeight(i);
                // clause not satisfed earlier but satisfed not 
                }else if(tempClauseStatus[i]==true && currentClauseStatus[i]==false){
                    increasedWeight+=clauses.getClauseWeight(i);
                }
            }
            return {reducedWeight,-increasedWeight};
        }
        // stops execution if exceeds given time
        bool checkTimeStopExecution(){
            time_t timeEnd = time(NULL);
            if(timeEnd-timeStart>55) // if we exceed 55 seconds we stop
                return true;
            return false;
        }
        // return random number in a range
        private: static int getRandonInRange(int lower,int upper) {
            return (rand() % (upper - lower + 1)) + lower; 
        }
};
int main(){
    timeStart = time(NULL); // store starting time
    ios::sync_with_stdio(0);cin.tie(0);cout.tie(0); // fast IO
    srand(time(NULL)); // seed
    string strOneLine,str;
    int inp;
    char ch; 
    cin>>ch;
    // ignore lines starting with 'c'
    while (ch=='c'){
        getline(cin,strOneLine); 
        cin>>ch;
    }
    int temp2;
    cin>>str>>totalVariables>>totalClauses; 
    clauseSet clauses; // clauseset object
    vector<int>input; // stores literals
    while(cin>>inp){
        if(inp==0){
            clause cl(input[0]);
            for(int idx=1;idx<input.size();idx++)
                cl.addLiteral(input[idx]);
            clauses.addClause(cl); // add clause
            input.clear();
        }else{
            input.emplace_back(inp); // add literal
        }    
    }   
    // this was taken from WALKSAT PAPER round(0.01875*totalVariables+2.8125)
    // solver object
    Solver localSearchSolver(clauses,round(0.01875*totalVariables+2.8125),10000,100);
    pair<int,vector<bool>>answer=localSearchSolver.solve();
    cout<<"s OPTIMUM FOUND\nv ";
    for(int i=1;i<=totalVariables;i++){
        if(answer.second[i]%2==false)
            cout<<"-";        
        cout<<i<<" ";        
    }
}