//Template begins
#include<bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
using namespace __gnu_pbds;
using namespace std;
#define fio ios_base::sync_with_stdio(false); cin.tie(NULL)
#define ll long long
#define lb lower_bound
#define ub upper_bound
#define pb push_back
#define fo(i,a,b) for(int i=a; i<b; i++)
#define all(v) (v).begin(),(v).end()
typedef pair<int,int> pii;
typedef pair<ll,ll> pll;
#define d0(x) cout<<(x)<<" "
#define d1(x) cout<<(x)<<endl
#define d2(x,y) cout<<(x)<<" "<<(y)<<endl
#define max3(a,b,c) max(max((a),(b)),(c))
#define max4(a,b,c,d) max(max((a),(b)),max((c),(d)))
#define min3(a,b,c) min(min((a),(b)),(c))
#define min4(a,b,c,d) min(min((a),(b)),min((c),(d)))
template<typename T>
using oset = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update>;
/*
    find_by_order() - Returns an iterator to the k-th largest element (counting from zero)
    order_of_key()  - The number of items in a set that are strictly smaller than our item
    Rest same as set
*/
const long double PI = 3.14159265358979323846264338;
const long long INF = 999999;
const long long INF1 = 1000000000;
const long long MOD = 1000000007;
// const long long MOD = 998244353;

ll mpow(ll a, ll b){
    a %= MOD;
    if(!b)
        return 1;
    ll temp = mpow(a, b/2);
    temp = (temp*temp) % MOD;
    if(b%2)
        return (a * temp) % MOD;
    return temp;
}


ll _pow(ll a, ll b){
    if(!b)
        return 1;
    ll temp = _pow(a, b/2);
    temp = (temp * temp);
    if(b%2)
        return (a * temp);
    return temp;
}

ll mod_in(ll n){
    return mpow(n, MOD-2);
}

ll cl(ll a, ll b){
    if(a%b)
        return 1 + a/b;
    return a/b;
}

ll gcd(ll a,ll b){if(b==0) return a;return gcd(b,a%b);}
//Template ends
vector<vector<pll> > v,tempv;		//This stores the graph
int flag;	//This variable is to keep track if there is a negative weight cycle or not.
ll n ,d;
vector<ll> h;	//This stores the distances calculated using bellmanford.
vector<vector<ll> > distt;



void bellman_ford()
{
	h[n]=0;
	for(int k=0; k<n; k++)
	{
		for(int i=0; i<n+1; i++)
		{
			for(pll x:tempv[i])
			{
				h[x.first]=min(h[x.first],h[i]+x.second);	
			}
		}
	}
	int f=-1;
	for(int i=0; i<n+1; i++)	//To check for negative weight cycle.
	{
		for(pll x:tempv[i])
		{
			if(h[x.first]>h[i]+x.second)	//Negative weight cycle confirmed.
			{
				f=1;
				break;
			}
		}
	}
	if(f==1)	
	{
		flag=1;
		return;
	}
	for(int i=0; i<n; i++)		//Changing the weights in actual graph.
	{
		for(int j=0; j<(int)v[i].size(); j++)
		{	
			v[i][j].second+=h[i]-h[v[i][j].first];
		}
	}
}



//Array based implementation.
void dijkstra_1()
{
	
	for(int s=0 ; s<n; s++)	
	{
		vector<ll> dist(n,INF);
		dist[s]=0;
		int node=s;
		int vis[n]={};	//Keeps track of the vertices that have already been considered.
		vis[s]=1;
		while(1)
		{
			for(pll x:v[node])
			{
				dist[x.first]=min(dist[x.first], dist[node]+x.second);
			}
			ll val=INF,pos=-1;	
			for(int i=0; i<n; i++)		//To find the next unvisited node with minimum distance.
			{
				if(vis[i]==0&&dist[i]<val)
				{
					val=dist[i];
					pos=i;
				}
			}
			if(pos==-1)		
				break;
			node=pos;
			vis[pos]=1;
		}
		for(int i=0; i<n; i++)
		{
			if(dist[i]!=INF&&d!=0)
				dist[i]+=h[i]-h[s];
			distt[s][i]=dist[i];
		}

	}
}

//End of case 1



//Binary heap based implementation.
vector<pll> w;		//w stores the heap, first value is the vertex number and second is the distance.
vector<ll> ind;		//Keeps track of the index of a vertex in w.

ll extractmin_binaryheap(ll & m)
{
	pll x=w[0];
	w[0]=w[m];
	ind[w[0].first]=0;
	m--;
	int pos=0;
	while((2*pos)+1<=m)		//Percolate down.
	{
		ll x=w[2*pos+1].second,y=INF;
		if(2*pos+2<=m)
			y=w[2*pos+2].second;
		if(min(x,y)>=w[pos].second)
			break;
		ll nextpos;
		if(min(x,y)==x)
			nextpos=2*pos+1;
		else
			nextpos=2*pos+2;
		ind[w[pos].first]=nextpos;
		ind[w[nextpos].first]=pos;
		swap(w[pos],w[nextpos]);
		pos=nextpos;
		
	}
	return x.first;
}

void decreasekey_binaryheap(ll id)	//id is the index in w of the key to be reduced.
{
	while(id>0)		//Percolate up.
	{
		ll par=(id-1)/2;
		if(w[id].second<w[par].second)
		{
			ind[w[id].first]=par;
			ind[w[par].first]=id;
			swap(w[id],w[par]);
			id=par;
			continue;	
		}	
		else
			break;
	}		
}




void dijkstra_2()
{
	for(int s=0; s<n; s++)
	{
		vector<ll> dist(n,INF);
		dist[s]=0;
		int node=s; 
		w.clear();
		w.pb({s,0});
		ind.assign(n,0);
		ind[s]=0;
		int c=1;
		for(int i=0; i<n; i++)
		{
			if(i==s)
				continue;
			w.pb({i,INF});
			ind[i]=c;
			c++;
		}

			
		ll m=n-1;
		while(m>=0)
		{
			int node=extractmin_binaryheap(m);
			for(pll x:v[node])
			{
				if(dist[x.first]>dist[node]+x.second)
				{
					ll id=ind[x.first];
					dist[x.first]=dist[node]+x.second;
					w[id].second=dist[x.first];
					decreasekey_binaryheap(id);
				}
			}
			
		}
		for(int i=0; i<n; i++)
		{
			if(dist[i]!=INF&&d!=0)
				dist[i]+=h[i]-h[s];
			distt[s][i]=dist[i];
		}


	}	
}

//End of case 2



//Binomial heap based implementation
struct node		//structure for binomial heap node.
{
	ll val,id,degree;		//val=distance of the vertex and id=vertex.
	node *par,*child,*sibling;
};

vector<node*> w1;	//Stores the pointer to each vertex.



node * addnode_binomialheap(ll val,ll id)	//Creates a new node and returns it.
{
	node *ptr=new node;	
	ptr->val=val,ptr->id=id,ptr->degree=0;
	ptr->par=NULL,ptr->child=NULL,ptr->sibling=NULL;
	return ptr;
}

node * union_binomialheap(node *h1, node *h2)	//To merge two heaps also maintaing the binomial heap property.
{
	node *p1=h1,*p2=h2,*hnew=NULL;		//hnew points to the new head after union operation.
	if(p1==NULL)
		return p2;
	if(p2==NULL)
		return p1;
	if(p1->degree<=p2->degree)
	{
		hnew=p1;
		p1=p1->sibling;
	}
	else
	{
		hnew=p2;
		p2=p2->sibling;
	}
	node *prev=hnew;
	while(p1!=NULL&&p2!=NULL)		//Merging two heaps.
	{
		if(p1->degree<=p2->degree)
		{
			prev->sibling=p1;
			prev=p1;
			p1=p1->sibling;
			
		}
		else
		{
			prev->sibling=p2;
			prev=p2;
			p2=p2->sibling;
		}
	}
	if(p1!=NULL)
	{
		while(p1!=NULL)
		{
			prev->sibling=p1;
			prev=p1;
			p1=p1->sibling;
		}
		prev->sibling=NULL;
	}
	else
	{
		while(p2!=NULL)
		{
			prev->sibling=p2;
			prev=p2;
			p2=p2->sibling;
		}
		prev->sibling=NULL;
	}
	prev=NULL;
	node *x=hnew, *nextx=hnew->sibling;
	while(nextx!=NULL)		//Making sure that there is atmost one binomial tree of any order after merging.
	{
		if(x->degree!=nextx->degree)
		{
			if(prev==NULL)
				hnew=x;
			prev=x;			
			x=x->sibling;
			nextx=nextx->sibling;
			continue;
		}
		node *nnextx=nextx->sibling;
		if(nnextx!=NULL && nnextx->degree==nextx->degree)	
		{
			if(prev==NULL)
				hnew=x;
			prev=x;
			x=x->sibling;
			nextx=nextx->sibling;
			continue;			
		}
		if(x->val<=nextx->val)
		{
			x->degree+=1;
			node *temp=x->child;
			x->sibling=nextx->sibling;
			x->child=nextx;
			nextx->sibling=temp;
			nextx->par=x;
			nextx=x->sibling;			
			continue;
		}
		nextx->degree+=1;
		node *temp=nextx->child;
		if(prev)
			prev->sibling=nextx;
		nextx->child=x;
		x->sibling=temp;
		x->par=nextx;
		x=nextx;
		nextx=x->sibling;
		
	}
	if(prev==NULL)
		hnew=x;
	return hnew;	
}



ll extractmin_binomialheap(node **head)
{
	node *p1=*head,*prev=NULL,*pos=NULL;	//pos points to the node before the node with the minimum value.
	ll mval=INF;
	while(p1!=NULL)
	{
		if(mval>(p1->val))
		{
			mval=p1->val;
			pos=prev;
		}
		prev=p1;
		p1=p1->sibling;
	}
	node *temp=NULL;
	if(pos==NULL)		//This is the case if head is the node with minimum value.
	{
		temp=(*head);
		*head=temp->sibling;
	}
	else
	{
		temp=pos->sibling;
		pos->sibling=temp->sibling;
	}
	temp->sibling=NULL;	
	node *t2=temp->child,*h2=NULL;
	temp->child=NULL;
	while(t2!=NULL)		//Reversing the child list as the order of trees should be in ascending order acc to my code.
	{
		t2->par=NULL;
		node *now=t2->sibling;
		t2->sibling=h2;
		h2=t2;
		t2=now;
	}
	*head=union_binomialheap(*head,h2);		//Union operation on child list and rootlist.
	temp->par=NULL;
	ll ans=temp->id;
	w1[ans]=NULL;
	free(temp);
	return ans;
	
	
	
}



void decreasekey_binomialheap(node *ptr)	
{
	while((ptr->par!=NULL)&&(ptr->val)<(ptr->par->val))		//Percolate up.
	{
		node *t1=ptr ,*t2=ptr->par;
		ll id1=t1->id, id2=t2->id, val1=t1->val, val2=t2->val;
		w1[id1]=t2,w1[id2]=t1;
		t1->id=id2,t1->val=val2;
		t2->id=id1,t2->val=val1;
		ptr=t2;		
	}
}







void dijkstra_3()
{
	
	for(int s=0; s<n; s++)
	{
		vector<ll> dist(n,INF);
		dist[s]=0;
		w1.assign(n,NULL);	//Stores pointer to each vertex.
		node *head=NULL;
		for(int i=0; i<n; i++)	
		{
			node *ptr=NULL;
			if(i==s)
				ptr=addnode_binomialheap(0,s);
			else
				ptr=addnode_binomialheap(INF,i);
			w1[i]=ptr;
			head=union_binomialheap(head,ptr);
			
		}
		for(int i=0; i<n; i++)
		{
			ll node=extractmin_binomialheap(&head);
			
			for(pll x:v[node])
			{
				if(dist[x.first]>dist[node]+x.second)
				{
					struct node *p=NULL;
					p=w1[x.first];
					dist[x.first]=dist[node]+x.second;
					p->val=dist[x.first];
					decreasekey_binomialheap(p);
				}	
			}
				
		}
		for(int i=0; i<n; i++)
		{
			if(dist[i]!=INF&&d!=0)
				dist[i]+=h[i]-h[s];
			distt[s][i]=dist[i];
		}

	}	
}

//End of binomial heap



//Fibonacci heap implementation

struct node2	//structure for fibonacci heap node.
{
	ll val,id,rank,mark;	//val stores distance and id stores index.
	node2 *left,*right,*par,*child;
};
vector<node2*> w2;	//stores pointer to each vertex.
ll total_nodes;

node2 * addnode_fibonacciheap(ll val, ll id)	//creates a new node and returns it.
{
	node2 *ptr=new node2;
	ptr->val=val,ptr->id=id;ptr->rank=0,ptr->mark=0;
	ptr->par=NULL,ptr->child=NULL,ptr->left=ptr,ptr->right=ptr;
	return ptr;	
}

node2 * insert_fibonacciheap(node2 *head,node2 *ptr)	//Inserts the node with pointer ptr into the heap.
{
	if(head==NULL)
		return ptr;
	if(head->left==head)
	{
		head->left=ptr,head->right=ptr;
		ptr->left=head,ptr->right=head;
		return head;
	}
	node2 * temp=head->right;
	head->right=ptr;
	ptr->left=head;
	ptr->right=temp;
	temp->left=ptr;
	return head;
}


void display(node2 *head)	//This is to display the root list. It is never used in my code. I just created it because it was required for debugging.
{
	if(head==NULL)
		return;
	node2 *ptr=head;
	cout<<ptr->id<<" ";
	ptr=ptr->right;
	while(ptr!=head)
	{
		cout<<ptr->id<<" ";
		ptr=ptr->right;
	}
}



void combine_fibonacciheap(node2 *p1, node2 *p2)	//This makes node with p1 as pointer as the parent of node with p2 as pointer.
{
	p2->left->right=p2->right;
	p2->right->left=p2->left;
	p2->par=p1;
	p2->left=p2,p2->right=p2;
	p1->child=insert_fibonacciheap(p1->child,p2);
	if((p2->val)<(p1->child->val))
		p1->child=p2;
	p1->rank++;
}


node2* consolidate_fibonacciheap(node2 *head)	//Used to consolidate the heap. Returns the new head.
{
	node2 *temp=head, *hnew=head;
	temp=temp->right;
	ll count=1;	//stores the number of nodes in the root list.
	while(temp!=head)	//Find the node with minimum value in the root list so we can make it as new head.
	{
		count++;
		if((temp->val)<(hnew->val))
			hnew=temp;
		temp=temp->right;
	}
	head=hnew;	
	float tval=log2(total_nodes);
	ll fval=tval;
	fval+=2;
	vector<node2*> pt(fval,NULL);		//This is to check if some tree with given rank is encountered or not while consolidating.
	temp=head;
	ll cnow=0;	//Stores the number of nodes in the root list that we have visited till now.
	temp=temp->right;
	while(cnow<count)
	{
		temp->mark=0,temp->par=NULL;
		if(pt[temp->rank]==NULL)	//if no node with the rank of current node exists at this moment.
		{
			cnow++;
			pt[temp->rank]=temp;
			temp=temp->right;
			continue;	
		}	
		node2 *p1=temp, *p2=pt[temp->rank];
		ll deg=temp->rank;
		if((p1->val)<=(p2->val))	//if the current node value is less than or equal to the value of previously encountered node(with same rank).
		{
			combine_fibonacciheap(p1,p2);
			pt[deg]=NULL;
			continue;
		}
		if(p1->right==p2&&p1->left==p2)		//only 2 nodes in the root list and both have same degree.
		{
			combine_fibonacciheap(p2,p1);
			pt[deg]=NULL;
			break;
		}
		p2->right->left=p2->left;		//if current node value is greater than the value of the previously encountered node(with same rank).
		p2->left->right=p2->right;
		p1->right->left=p2;
		p2->right=p1->right;
		p1->right=p2;
		p2->left=p1;
		pt[deg]=p1;
		temp=p2;
		
	}
	return head;
}




ll extractmin_fibonacciheap(node2 **head)		//Extracts node with minimum value and returns its id.
{
	node2 *ans=*head;
	node2 *p1=NULL,*p2=NULL;
	if(ans->child)
	{
		p1=ans->child;
		p2=p1->left;
	}
	if(p1==NULL&&ans->right==ans)		//If there is only one node in the entire heap.
	{
		ll id=ans->id;
		ans->right=NULL,ans->left=NULL;
		total_nodes--;
		w2[id]=NULL;
		free(ans);
		*head=NULL;
		return id;
	}
	if(p1!=NULL)	//if the child of head is not null then merging the child list into root list.
	{
	
		node2 *temp=ans->right;
		ans->right=p1;
		p1->left=ans;
		temp->left=p2;
		p2->right=temp;
	}
	ans->left->right=ans->right;	
	ans->right->left=ans->left;		
	*head=ans->right;
	ll id=ans->id;
	ans->right=NULL;
	ans->left=NULL;
	ans->child=NULL;
	ans->par=NULL;
	total_nodes--;
	free(ans);
	w2[id]=NULL;
	*head=consolidate_fibonacciheap(*head);		//To consolidate the root list and find the new head.

	
	return id;
}




void cut_fibonacciheap(node2 *ptr, node2 **head)	//Cut the node with pointer as ptr.
{	
	node2 *temp=*head;
	node2 *tchild=NULL, *tpar=ptr->par;
	if(ptr->right==ptr)		//if only single child.
	{
		tpar->child=NULL;
	}
	else		//more than 1 child case. 
	{
		tchild=ptr->right;
		tpar->child=tchild;
		ptr->right->left=ptr->left;
		ptr->left->right=ptr->right;
	}
	ptr->par=NULL;
	tpar->rank--;
	ptr->right=ptr,ptr->left=ptr;
	*head=insert_fibonacciheap(*head,ptr);		//inserting the node with ptr as pointer into the root list.
	if((ptr->val)<((*head)->val))	//Changing head if required.
		*head=ptr;
}




void cascadecut_fibonacciheap(node2 *ptr,node2 **head)		//recurssive function to cut the marked nodes.
{
	node2 *tpar=ptr->par;
	cut_fibonacciheap(ptr,head);
	if(tpar->par==NULL)	//if parent is the root.
	{
		tpar->mark=0;
		return;	
	}	
	if(tpar->mark==0)	//if parent is unmarked.
	{
		tpar->mark=1;
		return;
	}
	else	//if parent is marked and it is not root.
	{
		cascadecut_fibonacciheap(tpar,head);
	}
}










void decreasekey_fibonacciheap(node2 *ptr, node2 **head)
{
	if(ptr->par==NULL)	//if node with ptr as pointer is in the root list.
	{
		if((ptr->val)<(*head)->val)	//changing head if required.
			*head=ptr;
		return;
	}
	if((ptr->val)>=(ptr->par->val))	//if value of the considered node is greater than its parent's value.
		return;
	else
	{
		node2 *tpar=ptr->par;
		cut_fibonacciheap(ptr,head);	//Cut this node.
		if(tpar->mark==0)	//if parent is unmarked, mark it(if it is not in the root list) and return.
		{
			if(tpar->par!=NULL)
				tpar->mark=1;
			return;
		}
		if(tpar->par!=NULL)	//if parent is marked and not in root list.
			cascadecut_fibonacciheap(tpar,head);
	}
}









void dijkstra_4()
{
	distt.assign(n+1,vector<ll>(n+1,0));
	for(int s=0; s<n; s++)
	{
		vector<ll> dist(n,INF);
		dist[s]=0;
		node2 *head=NULL;
		w2.assign(n,NULL);		//Stores the pointer to each vertex.  
		total_nodes=0;
		for(int i=0; i<n; i++)
		{
			node2 *ptr=NULL;
			if(i==s)
				ptr=addnode_fibonacciheap(0,s);
			else
				ptr=addnode_fibonacciheap(INF,i);
			w2[i]=ptr;
			total_nodes++;
			head=insert_fibonacciheap(head,ptr);	
			if(i==s)
				head=w2[i];
		}
		
			
		for(int i=0; i<n; i++)
		{				
			ll id=extractmin_fibonacciheap(&head);
			//cout<<id<<"\n";
			for(pll x:v[id])
			{
				if(dist[x.first]>dist[id]+x.second)
				{
					dist[x.first]=dist[id]+x.second;
					node2 *p=w2[x.first];
					p->val=dist[x.first];
					decreasekey_fibonacciheap(p,&head);
				}
			}

		}
		
		
		for(int i=0; i<n; i++)
		{
			if(dist[i]!=INF&&d!=0)
				dist[i]+=h[i]-h[s];
			distt[s][i]=dist[i];
		}

		
		

	}	
}



int main(int argc,char *argv[])
{
	fio;
	int T;
	cin>>T;
	vector<double> ftime;
	clock_t tt;
	while(T--)
	{
		cin>>n>>d;
		flag=-1;
		v.assign(n,{});
		for(int i=0; i<n; i++)
		{
			for(int j=0; j<n; j++)
			{
				ll x;
				cin>>x;
				if(i==j)
					continue;
				if(d==0&&x<0)
					flag=1;
				if(x==INF)
					continue;
				v[i].pb({j,x});
			}
		}
	
		tempv=v;	//temp is a temporary graph used to implement bellmanford.
		vector<pll> now;
		for(int i=0; i<n; i++)		//Adding new vertex and putting 0-weight edges  from this vertex to all others.
			now.pb({i,0});
		tempv.pb(now);	
		h.assign(n+1,INF);	
		distt.assign(n+1,vector<ll>(n+1,0));		
		tt=clock();
		if(flag==1)
		{
			cout<<-1<<"\n";
			tt=clock()-tt;
			ftime.pb((double)tt/(double)(CLOCKS_PER_SEC));
			continue;
		}
		if(d!=0)
		{

			bellman_ford();
		}
		
		if(flag==1)
		{
			cout<<-1<<"\n";
			tt=clock()-tt;
			ftime.pb((double)tt/(double)(CLOCKS_PER_SEC));	
			continue;
		}
		int ch=-1;
		if(argc!=1)
			ch=atoi(argv[1]);
		if(argc==1||ch==4)
		{

			dijkstra_4();
			tt=clock()-tt;
			ftime.pb((double)tt/(double)(CLOCKS_PER_SEC));			
			for(int i=0; i<n; i++)
			{
				for(int j=0; j<n; j++)
					cout<<distt[i][j]<<" ";
				cout<<"\n";
			}			
		}
		else if(ch==1)
		{
			dijkstra_1();
			tt=clock()-tt;
			ftime.pb((double)tt/(double)(CLOCKS_PER_SEC));			
			for(int i=0; i<n; i++)
			{
				for(int j=0; j<n; j++)
					cout<<distt[i][j]<<" ";
				cout<<"\n";
			}
			
		}
		else if (ch==2)
		{
			dijkstra_2();
			tt=clock()-tt;
			ftime.pb((double)tt/(double)(CLOCKS_PER_SEC));			
			for(int i=0; i<n; i++)
			{
				for(int j=0; j<n; j++)
					cout<<distt[i][j]<<" ";
				cout<<"\n";
			}
			
		}	
		else if(ch==3)
		{
			dijkstra_3();
			tt=clock()-tt;
			ftime.pb((double)tt/(double)(CLOCKS_PER_SEC));			
			
			for(int i=0; i<n; i++)
			{
				for(int j=0; j<n; j++)
					cout<<distt[i][j]<<" ";
				cout<<"\n";
			}
			
		}
		else
		{
			dijkstra_4();
			tt=clock()-tt;
			ftime.pb((double)tt/(double)(CLOCKS_PER_SEC));			
			for(int i=0; i<n; i++)
			{
				for(int j=0; j<n; j++)
					cout<<distt[i][j]<<" ";
				cout<<"\n";
			}
			
		}			
	}
	double ttt=0;
	for(int i=0; i<(int)ftime.size(); i++)
	{
		cout<<ftime[i]<<" ";
		ttt+=ftime[i];
	}
	cout<<"\n";

}

