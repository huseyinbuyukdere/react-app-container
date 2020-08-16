import React from 'react';
import ReactAppContainer from '../../src';

const HomeRoute = () => {
  return (
    <div
      style={{
        height: "100%",
        width: "100%",
        display: "flex",
        justifyContent: "center",
        alignItems: "center",
      }}
    >
      <h1> Home Route </h1>
    </div>
  );
};

const AppsRoute = () => {
  return (
    <div
      style={{
        height: "100%",
        width: "100%",
        display: "flex",
        justifyContent: "center",
        alignItems: "center",
      }}
    >
      <h1> Application Route </h1>
    </div>
  );
};

const SettingsRoute = () => {
  return (
    <div
      style={{
        height: "100%",
        width: "100%",
        display: "flex",
        justifyContent: "center",
        alignItems: "center",
      }}
    >
      <h1> Settings Route </h1>
    </div>
  );
};

const SendMailRoute = () => {
  return (
    <div
      style={{
        height: "100%",
        width: "100%",
        display: "flex",
        justifyContent: "center",
        alignItems: "center",
      }}
    >
      <h1> Send Mail Route </h1>
    </div>
  )
}

const NoRouterVersion = () => {
  return (
    <div
      style={{
        height: "100%",
        width: "100%",
        display: "flex",
        justifyContent: "center",
        alignItems: "center",
      }}
    >
      <p>
        <h1>This is No Router Version,</h1>
        You can use only design, without adding routes to the component props.{" "}
        <br></br>
        <h5>You will see above the component code and design config. </h5>
        <h3>
          You can see the router version by changing disable/enable option above
        </h3>
      </p>
    </div>
  );
};


const DesignConfig = {
  sideBarMenu: [
    {
      iconName: "home",
      label: "Home",
      routeKey :"Home"
    },
    {
      iconName: "dashboard",
      label: "Dashboard",
    },
    {
      iconName: "apps",
      label: "Applications",
      routeKey :"Apps"
    },
    {
      iconName: "mail",
      label: "Mail",
      subMenuItemList: [
        {
          label: "Send Mail",
          iconName: "post_add",
          routeKey :'SendMail'
        },
        {
          label: "List Mail",
          iconName: "post_add",
        },
      ],
    },
    {
      iconComp: <h1>U</h1>,
      label: "Users",
      onClick: () => {
        alert("Users Clicked");
      },
    },
    {
      iconName: "settings",
      label: "Settings",
      routeKey :'Settings'
    },
  ],
  headerMenu: [
    {
      iconName: "room",
    },
    {
      iconName: "language",
      label: "Language",
      subMenuItemList: [
        {
          iconComp: <h4>TR</h4>,
          label: "Turkish",
          onClick: () => {
            alert("Turkish Clicked");
          },
        },
        {
          iconComp: <h4>FR</h4>,
          label: "French",
          onClick: () => {
            alert("English Clicked");
          },
        },
      ],
    },
  ],
  headerLeftContent: (
    <h5
      style={{
        color: "white",
        borderStyle: "solid",
        borderColor: "white",
        borderWidth: "1px",
        padding: "5px",
      }}
    >
      {" "}
      Here is Header Left Content Key. You can add what you want as
      Component
    </h5>
  ),
  sideBarHeaderContent: (
    <h3 style={{ fontFamily: "monospace" }}>Container & Your Logo</h3>
  ),
} 

const Routes = [{
  component :(<HomeRoute />),
  key : 'Home',
  label : 'Home Page',
  path :'/react-app-container/'                        
},
{
  component : (<AppsRoute />),
  key :'Apps',
  label : 'Application',
  path :'/react-app-container/Apps'
},
{
  component :(<SettingsRoute />),
  key :'Settings',
  label :'Settings',
  path : '/react-app-container/Settings'
},
{
  component :(<SendMailRoute />),
  key :'SendMail',
  label :'Send Mail Page',
  path : '/react-app-container/SendMail'
}]


function App() {
  return (
    <ReactAppContainer designConfig={DesignConfig} routes={Routes}/>
  );
}

export default App;
