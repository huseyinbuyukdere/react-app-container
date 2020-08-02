import * as React from 'react'
import { BrowserRouter as Router, Switch, Route } from 'react-router-dom'
import { ContainerRoute, DesignConfig } from './models'
import Container from './container'

interface MainProps {
    routes: ContainerRoute[]
    designConfig?: DesignConfig
}

const Main: React.FunctionComponent<MainProps> = (props) => {
    return (
        <Router>
            <Switch>
                {props.routes &&
                    props.routes.map((item: ContainerRoute) => {
                        return (
                            <Route path={item.path} exact={true}>
                                <Container
                                    routes={props.routes}
                                    designConfig={props.designConfig}
                                    selectedRoute={item}
                                >
                                    {item.component}
                                </Container>
                            </Route>
                        )
                    })}
            </Switch>
        </Router>
    )
}

export default Main
