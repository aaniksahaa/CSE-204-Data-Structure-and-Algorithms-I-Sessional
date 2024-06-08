#include<bits/stdc++.h>
using namespace std;

struct point{
    double x,y;
};
double dist(point a, point b)
{
    double dx = a.x-b.x;
    double dy = a.y-b.y;
    return sqrt(dx*dx+dy*dy);
}

double merge_dist(point arr[],int left, int mid, int right)
{

}

double mindist(point arr[], int start, int finish)
{
    if(finish-start==1)
    {
        return dist(arr[start],arr[finish]);
    }
    if(finish-start==2)
    {
        double ans = dist(arr[start],arr[start+1]);
        ans = min(ans,dist(arr[start+1],arr[start+2]));
        ans = min(ans,dist(arr[start],arr[start+2]));
        return ans;
    }

    int mid = (start+finish)/2;

    double ans = min(mindist(arr,start,mid),mindist(arr,mid+1,finish));

    return min(ans,merge_dist(arr,start,mid,finish);
}

int main()
{

    return 0;
}

