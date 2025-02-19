<H1>Space-Time Diagrams</H1>

%% insert note text below %%

Space-time diagrams are used to represent events ordering in distributed computations.

>[!important] Space-Time Diagram
A diagram is an oriented graph.
A graph node corresponds to events of the distributed computation being studied which is marked by a pair consisting of the event source identifier and the event number in the corresponding local event ledger. Graph edges are of two kinds.
An edge of the first kind links a node with the node having the same source and the succeeding number in the ledger.
An edge of the second kind links a sending event with the receiving event of the same message.

>[!info]- Example of Space-time diagram ([from](https://lamport.azurewebsites.net/pubs/time-clocks.pdf))
>![State-Time Diagram](https://www.researchgate.net/publication/237714712/figure/fig2/AS:654785850138624@1533124520274/Lamport-Space-Time-Diagram-extracted-from-28-c-1978-ACM.png)
>- $\mathtt{P}$, $\mathtt{Q}$, and $\mathtt{R}$ are participants
>- $\mathtt{p_1,p_2,p_3,p_4}$ are events entered in the ledger of $\mathtt{P}$
>- $\mathtt{q_1,q_2,q_3,q_4,q_5,q_6}$ are events entered in the ledger of $\mathtt{Q}$
>- $\mathtt{r_1,r_2,r_3,r_4}$ are events entered in the ledger of $\mathtt{R}$
>- wavy arrows connect the events of sending messages with the corresponding events of receiving messages; for example, $\mathtt{q}_4$ is an event of sending a message and $\mathtt{r}_3$ is the event of receiving this message