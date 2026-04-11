Build & Test Strategy                                                                                                                                                   
                                                                                                                                                                         
 Command: timeout 120 make agda                                                                                                                                          
                                                                                                                                                                         
 If timeout triggers: Proof refactor needed per lessons-learned.md:                                                                                                      
 - No function definitions in where clauses                                                                                                                              
 - Use records instead of nested tuples                                                                                                                                  
 - Consider extracting helpers to module level                                                                                                                           
 If something is Blocked, then we should stop and make a decision before continueing                                                                                                                                                                         
 ---                                                                                                                                                                     
 Verification                                                                                                                                                            
                                                                                                                                                                         
 After implementation:                                                                                                                                                   
 1. timeout 120 make agda succeeds                                                                                                                                       
 2. No SMP.!! at lines 3786, 3806, 3814 in RecTrace.agda                                                                                                                 
 3. Search for remaining SMP.!! - confirm only mechanical/product gaps remain                                                                                            

 Documentation                                                                                                                                                           
                                                                                                                                                                         
 - Any new lemmas have proof sketches                                                                                                                                    
 - Any remaining gaps documented in comments                                                                                                                             
 - Git commit message explains what was proven and what remains                                                                                                          

